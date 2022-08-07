//! This library contains an implementation for the simplification of boolean terms.
//!  
//! # Example
//! Consider the following boolean function
//! 
//! | A | B || C |
//! |---|---||---|
//! | 0 | 0 || 1 |
//! | 0 | 1 || 0 |
//! | 1 | 0 || 1 |
//! | 1 | 1 || 0 |
//! 
//! ```
//! // use the boolean expression from above
//! 
//! use quinemccluskey_rs::simplify_bool_term;
//! 
//! let minterms = vec![0, 2];
//! let n_variables = Some(2);
//! 
//! let simplified = simplify_bool_term(&minterms, n_variables);
//! assert_eq!(simplified, [(0b00, 0b01)]);
//! ```
//! Which corresponds to the function `C = B'`.
//! More about the function and especially the interpretation of its output can be read [here](simplify_bool_term).


use itertools::{Itertools, fold};
use std::collections::{HashMap, HashSet};




/// This function computes the hamming distance between two numbers with an optional mask
/// # Arguments
/// * `x` - First input
/// * `y` - Second input
/// * `mask` - Optional mask
///
/// # Output
/// The hamming distance of `mask & x` and `mask & y`
/// 
/// # Examples
/// ```
/// use quinemccluskey_rs::hamming;
/// 
/// assert_eq!(hamming(0b01, 0b11, None), 1);
/// assert_eq!(hamming(0b101, 0b001, Some(0b011)), 0);
/// ```
/// 
pub fn hamming(x: u16, y: u16, mask: Option<u16>) -> u32 {
    if let Some(mask) = mask {
        return (mask & (x ^ y)).count_ones();
    }
    return (x ^ y).count_ones();
}

/// This function returns the index of the first bit difference between two numbers with an optional mask
/// # Arguments
/// * `x` - First input
/// * `y` - Second input
/// * `mask` - Optional mask
///
/// # Output
/// The position of the first different bit between `mask & x` and `mask & y`.
/// The position is counted from the least significant bit which itself has a position of `0`.
/// 
/// # Examples
/// ```
/// use quinemccluskey_rs::find_first_difference;
/// 
/// assert_eq!(find_first_difference(0b01, 0b11, None), 1);
/// assert_eq!(find_first_difference(0b0101, 0b1001, Some(0b1011)), 3);
/// 
/// ```
pub fn find_first_difference(x: u16, y: u16, mask: Option<u16>) -> usize {
    debug_assert!(hamming(x, y, mask) >= 1, "Make sure that there is at least one different bit between mask & (x ^ y), otherwise this function will panic in optimized builds");

    let to_check = match mask {
        Some(m) => m & (x ^ y),
        None => (x ^ y),
    };

    for i in 0..u16::BITS as usize {
        if to_check & (1 << i) != 0 {
            return i;
        }
    }
    panic!("There is no bit set in {:0b}", to_check);
}

type MinTerm = u16;
type GroupTable = HashMap<usize, Vec<(Vec<MinTerm>, MinTerm, MinTerm)>>;
type VariableNumber = u16;


/// This function simplifies a given list of minterms
/// 
/// # Arguments
/// * `minterms` - The list of minterms that evaluate to true, for example if the binary function is
/// 
/// | A | B || C |
/// |---|---||---|
/// | 0 | 0 || 1 |
/// | 0 | 1 || 0 |
/// | 1 | 0 || 1 |
/// | 1 | 1 || 0 |
/// 
/// The canonical form can be written as `A'B' + AB'`.
/// The input for minterms would be `[0, 2]`, because the rows which have a 1 in the C column have these binary numbers
/// 
/// * `n_variables` - Optional argument for the number of variables, in the example above it would be `Some(2)`.
/// If nothing is given here, the number of variables inferred is `log2(max(minterms) + 1)` which is not always correct
/// 
/// # Output
/// A list of tuples
/// Each of the tuples describe a minterm from the solution expression
/// The first number in the tuple describes all set variables and
/// the second number in the tuple describes all unset variables.
/// 
/// For example if the output is `[(0b11, 0b00), (0b00, 0b01)]`,
/// the solution is `AB + B'` if `A` is the first variable and `B` is the second.
/// 
/// # Examples
/// ```
/// // use the boolean expression from above
/// // | A | B || C |
/// // |---|---||---|
/// // | 0 | 0 || 1 |
/// // | 0 | 1 || 0 |
/// // | 1 | 0 || 1 |
/// // | 1 | 1 || 0 |
/// 
/// use quinemccluskey_rs::simplify_bool_term;
/// 
/// let minterms = vec![0, 2];
/// let n_variables = Some(2);
/// 
/// let simplified = simplify_bool_term(&minterms, n_variables);
/// assert_eq!(simplified, [(0b00, 0b01)]);
/// ```
/// 
pub fn simplify_bool_term(minterms: &Vec<MinTerm>, n_variables: Option<u16>) -> Vec<(u32, u32)> {
    // apply the quine-mccluskey algorithm
    let (prime_implicants, n_variable_cnd) = compute_prime_implicants(minterms).unwrap();
    
    let n_variables = match n_variables {
        Some(n) => n,
        None => n_variable_cnd,
    };


    // simplify using petrick's method
    let simplification = compute_simplified_term(&prime_implicants, n_variables);

    // now compute the bit flag vector
    let mut result = Vec::new();
    for idx in simplification {
        let (_, assignment, mask) = &prime_implicants[idx];
        let mut set_states: u32 = 0;
        let mut unset_states: u32 = 0;

        for var in 0..n_variables {
            if (mask >> var) & 0b1 == 1 {
                if (assignment >> var) &0b1 == 1 {
                    set_states |= 0b1 << var
                } else {
                    unset_states |= 0b1 << var
                }
            }
        }
        result.push((set_states, unset_states))
    }

    return result;
}

fn compute_prime_implicants(minterms: &Vec<MinTerm>) -> Result<(Vec<(Vec<MinTerm>, MinTerm, MinTerm)>, VariableNumber), &'static str> {
    // sort into groups
    let mut group_table: GroupTable = HashMap::new();
    let mut max_minterm = 0;

    // Find the max index minterm and initialize the hashmap
    for minterm in minterms {
        if *minterm > max_minterm {
            max_minterm = *minterm;
        }
        let number_of_ones = hamming(*minterm, 0, None);
        let group = group_table.entry(number_of_ones as usize).or_insert(vec![]);

        // push the minterm descriptor, the current assignment and the bit mask
        group.push((vec![*minterm], *minterm, MinTerm::MAX));
    }

    let mut original_table: GroupTable = group_table;

    // Reduce into groups if the hamming distance of consecutive groups is 1
    // until no longer possible
    loop {
        let mut next_table: GroupTable = HashMap::new();
        let mut group: usize = 0;

        for (g1, g2) in original_table.keys().sorted().tuple_windows() {
            let g1_entry = &original_table[g1];
            let g2_entry = &original_table[g2];

            let mut temp_hm: HashMap<Vec<MinTerm>, (usize, MinTerm, MinTerm)> = HashMap::new();

            for (cnd1, minterm1, mask1) in g1_entry {
                for (cnd2, minterm2, mask2) in g2_entry {
                    // compute the combined mask
                    if mask1 == mask2 {
                        let mask = mask1 & mask2;
                        if hamming(*minterm1, *minterm2, Some(mask)) == 1 {
                            // merge the two minterms
                            let different_bit_pos =
                                find_first_difference(*minterm1, *minterm2, Some(mask));

                            let new_mask = mask & !(1 << different_bit_pos);
                            let new_assignment = *minterm1;
                            let mut new_descriptors = vec![];

                            new_descriptors.extend(cnd1);
                            new_descriptors.extend(cnd2);
                            new_descriptors.sort();

                            // add new merged entry (removes duplicates)
                            temp_hm.insert(new_descriptors, (group, new_assignment, new_mask));
                        }
                    }
                }
            }
            if !temp_hm.is_empty() {
                group += 1;
            }

            for (descriptor, (group, assignment, mask)) in temp_hm.drain() {
                let entry = next_table.entry(group).or_insert(vec![]);
                entry.push((descriptor, assignment, mask));
            }
        }
        if group == 0 {
            // reduction complete
            break;
        }
        original_table = next_table;
    }

    let mut prime_implicants = Vec::new();
    for (_, prime) in original_table.drain() {
        prime_implicants.extend(prime);
    }

    return Ok((prime_implicants, (max_minterm as f32 + 1.).log2().floor() as u16));
}

fn needed_variables(n_variables: u16, assignment: u16, mask: u16) -> Vec<String> {
    let mut variables: Vec<String> = vec!();

    for cnd in 0..n_variables {
        if mask >> cnd & 0b1 == 1 {
            let offset = n_variables - cnd -1;
            let current_char: char = char::from_u32(('A' as u16 + offset) as u32).expect("Not a char");
            
            if assignment >> cnd & 0b1 == 1 {
                variables.push(format!("{}", current_char));
            } else {
                variables.push(format!("{}'", current_char));
            }
        }
    }
    return variables;
}

fn compute_simplified_term(prime_implicants: &Vec<(Vec<MinTerm>, u16, u16)>, n_variables: u16) -> Vec<usize> {
    // 1. compute essential minterms
    // compute a u8 matrix where each column corresponds to a minterm and each row to a prime implicant

    let mut bool_matrix: HashMap<MinTerm, (u16, Vec<usize>)> = HashMap::new();
    let mut prime_terms: HashSet<usize> = HashSet::new();

    for (i, (descriptors, _, _)) in prime_implicants.iter().enumerate()  {
        for desc in descriptors {
            let (counter, idx) = bool_matrix.entry(*desc).or_insert((0, Vec::new()));
            *counter += 1;
            idx.push(i);
            prime_terms.insert(i);
        }
    }

    let mut essential_prime_terms = HashSet::new();
    for (counter, term_idx) in bool_matrix.values() {
        if *counter == 1 {
            // The vector must contain exactly one element if counter == 1
            
            essential_prime_terms.insert(term_idx[0]);
            prime_terms.remove(&term_idx[0]);
        }
    }

    // If there is no nonessential prime term, we can terminate because
    // all prime terms are essential
    if prime_terms.len() == 0 {
        return essential_prime_terms.into_iter().collect();
    }

    // now rebuild the matrix without essential primes
    let mut bool_matrix: HashMap<MinTerm, Vec<usize>> = HashMap::new();
    for i in prime_terms  {
        let (descriptors, _, _) = &prime_implicants[i];
        for desc in descriptors {
            let idx = bool_matrix.entry(*desc).or_insert(Vec::new());
            idx.push(i);
        }
    }

    let mut distributives: Vec<Vec<Vec<usize>>> = bool_matrix
    .drain()
    .map(|(_, b)| 
        b
            .iter()
            .map(|&a| vec!(a))
            .collect()
    )
    .collect::<Vec<Vec<Vec<usize>>>>();


    let first = distributives.swap_remove(0);
    let mut distributed = fold(distributives, first, |a, b| distribute(a,b));


    // Now select shortest minterms
    let short_len = distributed[0].len();
    let candidates = distributed.drain(..).take_while(|cnd| cnd.len() <= short_len).collect::<Vec<Vec<usize>>>();

    if candidates.len() == 0 {
        // only one entry it must be minimal
        for term in &candidates[0] {
            essential_prime_terms.insert(*term);
        }
        return essential_prime_terms.drain().collect();
        // return candidates.swap_remove(0);
    }

    // else select the entry with fewest literals
    let mut best_entry = 0;
    let mut best_literal_count = usize::MAX;

    for (i, cnd) in candidates.iter().enumerate() {
        let count = cnd
            .iter()
            .map(|&idx| &prime_implicants[idx])
            .map(|(_, a, b)| needed_variables(n_variables, *a, *b).len())
            .sum::<usize>();
        
        if count < best_literal_count {
            best_literal_count = count;
            best_entry = i;
        }
    }

    for term in &candidates[best_entry] {
        essential_prime_terms.insert(*term);
    }
    return essential_prime_terms.drain().collect();
}

// computes the product (A + B) * (X + Y) = AX + AY + BX + BY
// and simplifies it
fn distribute<T>(mut left: Vec<Vec<T>>, right: Vec<Vec<T>>) -> Vec<Vec<T>>
    where T:std::clone::Clone + std::cmp::PartialEq + std::cmp::Ord + std::fmt::Debug
{
    // compute product
    let product: Vec<Vec<T>> = left
        .drain(..)
        .cartesian_product(right)
        .map(|(mut a, b)| {a.extend(b); a})
        .dedup() // X + X = X
        .map(|mut a | {
            a.sort();
            a.dedup(); // XX = X
            a
        })
        .sorted_by(|a, b| Ord::cmp(&a.len(), &b.len()))
        .collect();
    
    // simplify X + XY = X
    let mut del = Vec::new();
    for (i, term1) in product.iter().enumerate() {
        for (j, term2) in product[i+1..].iter().enumerate() {
            // term1 is always shorter than term2 because
            // the the entries are sorted_by(len)
            
            // is true if all entries of term1 are also in term2
            // ONLY works if term1 and term2 are sorted and term1.len() <= term2.len()
            debug_assert!(term1.len() <= term2.len(), "The length of term1 is greater than of term2");
            debug_assert!(term1.iter().tuple_windows().map(|(a,b)| a < b).all(|a| a == true), "Term1 is not sorted");
            debug_assert!(term2.iter().tuple_windows().map(|(a,b)| a < b).all(|a| a == true), "Term2 is not sorted");

            // check with binary search if all elements of term1 are in term2
            let term1_in_term2 = term1.iter().map(|a| binary_contains(&term2, &a)).all(|a| a.is_ok());
            if term1_in_term2 {
                // delete XY
                del.push(i+j+1)
            }
        }
    }
    del.sort();
    del.dedup();

    let mut product = product;
    for entry in del.into_iter().rev() {
        product.swap_remove(entry);
    }
    return product;
}

fn binary_contains<T>(xs: &Vec<T>, x: &T) -> Result<usize, usize>
where T: std::cmp::PartialOrd
{
    let mut size = xs.len();
    if size == 0 {
        return Err(0);
    }

    let mut base: usize = 0;
    while size > 1 {
        let half = size / 2;
        let mid = base + half;
        if xs[mid] <= *x {
            base = mid;
        }
        size = size >> 1; // halve the interval
    }

    if xs[base] == *x {
        return Ok(base);
    }
    Err(base + (xs[base] < *x) as usize)
}



#[cfg(test)]
mod tests {
    use super::*;
        #[test]
    fn simplifies_if_all_one() {
        let minterms = (0..8).collect::<Vec<u16>>();
        assert_eq!(simplify_bool_term(&minterms, None), [(0,0)]);
    }
    #[test]
    fn simplifies_if_all_zero() {
        let minterms = vec!();
        assert_eq!(simplify_bool_term(&minterms, None), []);
    }
    #[test]
    fn simplify_1() {
        //  0 0 | 1
        //  0 1 | 1
        //  1 0 | 0
        //  1 1 | 0
        //  A' is the minimal solution
        let minterms = vec!(0, 1);
        assert_eq!(simplify_bool_term(&minterms, Some(2)), [(0, 2)]);
    }
    #[test]
    fn simplify_2() {
        //  0 0 | 1
        //  0 1 | 0
        //  1 0 | 1
        //  1 1 | 0
        //  B' is the minimal solution
        let minterms = vec!(0, 2);
        assert_eq!(simplify_bool_term(&minterms, Some(2)), [(0, 1)]);
    }
    #[test]
    fn simplify_3() {
        //  0 0 | 0
        //  0 1 | 1
        //  1 0 | 1
        //  1 1 | 0
        //  A'B + AB' is the minimal solution
        let minterms = vec!(1, 2);
        let test_solution = simplify_bool_term(&minterms, Some(2));
        let solution = [(1, 2), (2, 1)];
        assert!(test_solution.iter().all(|x| solution.contains(x)) && solution.iter().all(|x| test_solution.contains(x)));
    }
    #[test]
    fn test_order() {
        let minterms = vec!(1, 2, 10, 30, 16, 24, 30);
        let solution1 = simplify_bool_term(&minterms, None);
        let solution2 = simplify_bool_term(&minterms.into_iter().rev().collect(), None);

        assert!(solution1.iter().all(|x| solution2.contains(x)) && solution2.iter().all(|x| solution1.contains(x)));
    }

    #[test]
    fn test_doubles() {
        let minterms = vec!(1, 2, 3, 3, 2, 1, 2, 3);
        let test_solution = simplify_bool_term(&minterms, Some(2));
        let solution = [(1,0), (2,0)];

        assert!(solution.iter().all(|x| test_solution.contains(x)) && test_solution.iter().all(|x| solution.contains(x)));
    }
}

# Quine-McCluskey-rs
An implementation of the Quine-McCluskey algorithm in pure rust.

## Add it to your project
```bash
cargo add quinemccluskey-rs
```

## How to use
Assume you want to minimize the following function

| A | B | *X* |
|---|---|---|
| 0 | 0 | 1 |
| 0 | 1 | 0 |
| 1 | 0 | 1 |
| 1 | 1 | 0 |

Then the terms that evaluate to *`1`* are the terms which binary representation is `0` and `2`.
```rust
use quinemccluskey_rs::simplify_bool_term;

let minterms = vec![0, 2];
let n_variables = Some(2);

let simplified = simplify_bool_term(&minterms, n_variables);

assert_eq!(simplified, [(0b00, 0b01)]);
```
The output says that the solution has one minterm,
where only B is present in its negated form.
To conclude `X = B'`.

If instead the solution was `[(0b110, 0b000), (0b000, 0b001)]`,
it would translate to `X = AB + C'`

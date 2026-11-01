-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_eq_21
-- name    : CleveDiVincenzo.Schumacher.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:21.338991+00:00
-- url     : https://prove2.me/theorems/7516288c-3d0b-4c8d-a031-0242b7e4b8cb
-- title:
--   Eq. (21) — $f(x)$ lies in the block of its weight
-- statement:
--   Let $n\ge0$ and let $x$ be an $n$-bit string with $m=\sum_{k=0}^{n-1}x_k$ ones. Then $y=f(x)$ satisfies
--   $$
--   \sum_{i=0}^{m-1}\binom ni\;\le\; y\;<\;\sum_{i=0}^{m}\binom ni .
--   $$
--
--   This is the inequality that lets the first loop of the inverse programs recover the weight $m$ of $x$ from $y$ alone.
--
--   Differences from the source:
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - generalization: n ≥ 1 implicitly (n qubits) → every n : ℕ, including n = 0; reason: the n ≥ 1 cases are exactly the paper's claim; n = 0 (one empty string) holds as well
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III B, Eqs. (21)–(22), p.15

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace CleveDiVincenzo.Schumacher

/-- **Eq. (21)** (Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum
computation*, arXiv:quant-ph/9603009v1, §III B, p.15): for an `n`-bit string `x` with
`m = Σ_{k=0}^{n−1} x_k` ones (Eq. (22)), its image `y = f(x)` satisfies
`Σ_{i=0}^{m−1} C(n,i) ≤ y < Σ_{i=0}^{m} C(n,i)`.

**Formalization Note** `x < 2^n` is the `n`-bit string `x_{n−1} … x_0`; `blockStart n m` is
`Σ_{i=0}^{m−1} C(n,i)`, so the upper bound is `blockStart n (m + 1)`. -/
theorem eq_21 (n x : ℕ) (hx : x < 2 ^ n) :
    blockStart n (weight x) ≤ schumacher n x ∧
      schumacher n x < blockStart n (weight x + 1) := by sorry

end CleveDiVincenzo.Schumacher

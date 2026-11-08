-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_eq_23
-- name    : CleveDiVincenzo.Schumacher.eq_23
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:21:14.767335+00:00
-- url     : https://prove2.me/theorems/e8116b11-f39f-42b1-bf48-2cb6c1770d79
-- title:
--   Eq. (23) — bounds on the index $I[x,n,m]$
-- statement:
--   Let $0\le p<n$ and let $x$ be an $n$-bit string whose leading $p$ bits are zeros and whose next bit is a one ($x_j=0$ for $n-1-p<j\le n-1$, $x_{n-p-1}=1$), with $m$ ones. Then
--   $$
--   \binom{n-p-1}{m}\;\le\; I[x,n,m]\;<\;\binom{n-p}{m}.
--   $$
--
--   Since these intervals are disjoint for different $p$, the index alone determines the position of the leading one of $x$; the inverse programs test exactly this inequality.
--
--   Differences from the source:
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - encoding: x = 0…0 1 x′ (p zeros, a 1, then an (n−p−1)-bit string x′; Eq. (8)) with m ones → x = 2^{n−p−1} + x′ with p < n and x′ < 2^{n−p−1}; m = weight x; reason: the same strings written as numbers
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III B, Eq. (23), p.15

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace CleveDiVincenzo.Schumacher

/-- **Eq. (23)** (Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum
computation*, arXiv:quant-ph/9603009v1, §III B, p.15): if the leading `p` bits of the `n`-bit
string `x` are zeros and the next bit is a 1 (`x_j = 0` for `n − 1 − p < j ≤ n − 1`,
`x_{n−p−1} = 1`), and `x` has `m` ones, then
`C(n − p − 1, m) ≤ I[x, n, m] < C(n − p, m)`.

**Formalization Note** As in `eq_9`, such an `x` is `2^{n−p−1} + x′` with `x′ < 2^{n−p−1}`,
`p < n`, and `m = weight x`. -/
theorem eq_23 (n p x' : ℕ) (hp : p < n) (hx' : x' < 2 ^ (n - p - 1)) :
    let x := 2 ^ (n - p - 1) + x'
    (n - p - 1).choose (weight x) ≤ index n x ∧ index n x < (n - p).choose (weight x) := by sorry

end CleveDiVincenzo.Schumacher

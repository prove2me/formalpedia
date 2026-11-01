-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_eq_9
-- name    : CleveDiVincenzo.Schumacher.eq_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:22.743831+00:00
-- url     : https://prove2.me/theorems/87fafabe-2af7-46b0-b04c-c1748f21170c
-- title:
--   Eq. (9) — recursion of the index $I[x,n,m]$
-- statement:
--   Let $0\le p<n$ and let $x=0\cdots0\,1\,x'$ be the $n$-bit string consisting of $p$ zeros, a one, and an $(n-p-1)$-bit string $x'$. If $x$ has $m$ ones (so $x'$ has $m-1$), then
--   $$
--   I[x,n,m]=\binom{n-p-1}{m}+I[x',\,n-p-1,\,m-1].
--   $$
--
--   Iterating this recursion gives the closed form (11) of the index, and it is the step the third loop of the inverse programs performs bit by bit.
--
--   Differences from the source:
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - encoding: x = 0…0 1 x′ (p zeros, a 1, then an (n−p−1)-bit string x′; Eq. (8)) with m ones → x = 2^{n−p−1} + x′ with p < n and x′ < 2^{n−p−1}; m = weight x; reason: the same strings written as numbers
--   - encoding: I[x′, n − p − 1, m − 1] → index (n − p − 1) x′; reason: index takes the weight of its argument, and x′ has m − 1 ones
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §II, Eqs. (8)–(9), p.9

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace CleveDiVincenzo.Schumacher

/-- **Eq. (9)** (Cleve, DiVincenzo, *Schumacher's quantum data compression as a quantum
computation*, arXiv:quant-ph/9603009v1, §II, p.9): for the `n`-bit string
`x = 0…0 1 x′` (`p` zeros, then a 1, then an `(n − p − 1)`-bit string `x′`; Eq. (8)) with `m`
ones, `I[x, n, m] = C(n − p − 1, m) + I[x′, n − p − 1, m − 1]`.

**Formalization Note** The string `x = 0^p 1 x′` is the number `x = 2^{n−p−1} + x′` with
`x′ < 2^{n−p−1}` and `p < n`. The weight is not an argument of `index`: `index n x` is
`I[x, n, m]` with `m = weight x`, and `index (n − p − 1) x′` is `I[x′, n − p − 1, m − 1]`, since
`x′` has `m − 1` ones. -/
theorem eq_9 (n p x' : ℕ) (hp : p < n) (hx' : x' < 2 ^ (n - p - 1)) :
    let x := 2 ^ (n - p - 1) + x'
    index n x = (n - p - 1).choose (weight x) + index (n - p - 1) x' := by sorry

end CleveDiVincenzo.Schumacher

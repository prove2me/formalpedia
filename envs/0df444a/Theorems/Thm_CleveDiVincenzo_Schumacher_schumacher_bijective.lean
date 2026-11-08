-- Prove2me | Theorems.Thm_CleveDiVincenzo_Schumacher_schumacher_bijective
-- name    : CleveDiVincenzo.Schumacher.schumacher_bijective
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:21:37.664114+00:00
-- url     : https://prove2.me/theorems/839e61d9-c66d-4a0d-b5f9-ce4baee07b79
-- title:
--   §III B, p.13 — the Schumacher function is a bijection of $\{0,\dots,2^n-1\}$
-- statement:
--   For every $n\ge0$, the Schumacher coding function $f$ maps the set $\{0,1,\dots,2^n-1\}$ of $n$-bit strings bijectively onto itself.
--
--   Bijectivity is what makes an in-place reversible implementation possible: "no record of the initial state, or of the state of the work bits, needs to be retained at the end; they are completely deducible from the output".
--
--   Differences from the source:
--   - encoding: an n-bit string x_{n−1} … x_0 (x_{n−1} first, x_p the p-th bit) → the natural number x < 2^n, with x_k = Nat.testBit x k; reason: p.6 and Eq. (11), p.9: the string is the binary number; same strings
--   - reading: "preserve lexicographical ordering within each block" (p.8) → index n x = number of z < 2^n with weight z = weight x and z < x (numerical order); reason: for fixed-length strings written most significant bit first, lexicographic order is numerical order; Eqs. (7)–(9) and (11) use this order
--   - generalization: n ≥ 1 implicitly (n qubits) → every n : ℕ, including n = 0; reason: the n ≥ 1 cases are exactly the paper's claim; n = 0 (one empty string) holds as well
-- source:
--   Cleve, DiVincenzo, Schumacher's quantum data compression as a quantum computation, arXiv:quant-ph/9603009v1, §III B, p.13 ("the Schumacher function is bijective"); §II, p.8 ("the mapping must be 1-to-1 (i.e., a bijection)")

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace CleveDiVincenzo.Schumacher

/-- **The Schumacher function is bijective** (Cleve, DiVincenzo, *Schumacher's quantum data
compression as a quantum computation*, arXiv:quant-ph/9603009v1, §III B, p.13; also §II, p.8,
"the mapping must be 1-to-1 (i.e., a bijection)"): `f` of Eq. (6) maps the set
`{0, …, 2^n − 1}` of `n`-bit strings bijectively onto itself. -/
theorem schumacher_bijective (n : ℕ) :
    Set.BijOn (schumacher n) (Set.Iio (2 ^ n)) (Set.Iio (2 ^ n)) := by sorry

end CleveDiVincenzo.Schumacher

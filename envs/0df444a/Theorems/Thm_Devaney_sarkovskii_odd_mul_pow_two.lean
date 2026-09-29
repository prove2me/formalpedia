-- Prove2me | Theorems.Thm_Devaney_sarkovskii_odd_mul_pow_two
-- name    : Devaney.sarkovskii_odd_mul_pow_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:32:34.744622+00:00
-- url     : https://prove2.me/theorems/8ce8154c-9594-4f21-96d9-cb20892bf82a
-- title:
--   Theorem 10.2, mixed case
-- statement:
--   Let $f$ be continuous with a periodic point of prime period $p \cdot 2^{m}$, where $p > 1$ is odd. Then $f$ has a periodic point of prime period $\ell$ for every $\ell$ with $p\cdot 2^{m} \triangleright \ell$.
--
--   This is the remaining case of Theorem 10.2; Devaney reduces it to the odd and power-of-two cases by passing to iterates of $f$, leaving the reductions as exercises.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 65, proof of Theorem 10.2 (case n = p·2^m, reductions in Exercises 2–3, p. 68)

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem sarkovskii_odd_mul_pow_two (f : ℝ → ℝ) (hf : Continuous f) (p m : ℕ) (hp : Odd p)
    (hp1 : 1 < p) (h : ∃ x, HasPrimePeriod f x (p * 2 ^ m)) (l : ℕ)
    (hl : SarkovskiiPrecedes (p * 2 ^ m) l) :
    ∃ x, HasPrimePeriod f x l := by sorry
end Devaney

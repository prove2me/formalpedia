-- Prove2me | Theorems.Thm_Devaney_sarkovskii_pow_two
-- name    : Devaney.sarkovskii_pow_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:27:47.895981+00:00
-- url     : https://prove2.me/theorems/72dce3fd-6402-4537-9150-12d358ea2a9b
-- title:
--   Theorem 10.2, power-of-two case
-- statement:
--   Let $f$ be continuous with a periodic point of prime period $2^{m}$. Then $f$ has a periodic point of prime period $2^{a}$ for every $a < m$.
--
--   Devaney's argument passes to $g = f^{2^{a-1}}$, for which the hypothesis provides a point of period $2^{m-a+1}$, hence a point of period two; that point has period $2^{a}$ for $f$.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 65, proof of Theorem 10.2 (case n = 2^m)

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem sarkovskii_pow_two (f : ℝ → ℝ) (hf : Continuous f) (m : ℕ)
    (h : ∃ x, HasPrimePeriod f x (2 ^ m)) (a : ℕ) (ha : a < m) :
    ∃ x, HasPrimePeriod f x (2 ^ a) := by sorry
end Devaney

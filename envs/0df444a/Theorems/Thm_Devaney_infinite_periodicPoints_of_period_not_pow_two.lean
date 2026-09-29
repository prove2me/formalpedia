-- Prove2me | Theorems.Thm_Devaney_infinite_periodicPoints_of_period_not_pow_two
-- name    : Devaney.infinite_periodicPoints_of_period_not_pow_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T10:41:49.073439+00:00
-- url     : https://prove2.me/theorems/562c2bdd-548b-49f3-985f-adc2c33dad21
-- title:
--   Remark 1 after Theorem 10.2 — a non-dyadic period forces infinitely many periodic points
-- statement:
--   If a continuous map of the line has a periodic point whose prime period is not a power of two, then it has infinitely many periodic points. Equivalently, a continuous map with only finitely many periodic points has all its periods equal to powers of two — the fact behind the period-doubling route to chaos.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.10, p. 62, Remark 1 following Theorem 10.2

import Mathlib
import Definitions.Def_Devaney_sarkovskii

namespace Devaney
theorem infinite_periodicPoints_of_period_not_pow_two (f : ℝ → ℝ) (hf : Continuous f) (n : ℕ)
    (h : ∃ x, HasPrimePeriod f x n) (hn : ∀ m : ℕ, n ≠ 2 ^ m) :
    {x : ℝ | ∃ k > 0, f^[k] x = x}.Infinite := by sorry
end Devaney

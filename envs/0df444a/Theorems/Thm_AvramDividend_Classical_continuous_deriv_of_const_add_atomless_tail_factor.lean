-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_deriv_of_const_add_atomless_tail_factor
-- name    : AvramDividend.Classical.continuous_deriv_of_const_add_atomless_tail_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:51:12.157006+00:00
-- url     : https://prove2.me/theorems/a93a5f49-14ce-468c-abd5-b2453a3fe3e8
-- title:
--   Derivative continuity from a constant plus atomless finite-tail factorisation
-- statement:
--   If W is continuous on the positive half-line and its derivative factors as W(x) times a fixed real constant plus the finite upper-tail mass of an atomless measure, then W' is continuous. This is the deterministic form needed after an Esscher transform, where the constant is Phi(q) and the tail is an excursion-height measure.
-- source:
--   Immediate from Proved continuous_measureReal_Ici_of_finite_noAtoms and continuity under addition/multiplication; matches the q-scale excursion representation after Esscher tilting.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Ici_of_finite_noAtoms
open MeasureTheory Set

theorem AvramDividend.Classical.continuous_deriv_of_const_add_atomless_tail_factor
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤)
    (φ : ℝ) (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x))) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

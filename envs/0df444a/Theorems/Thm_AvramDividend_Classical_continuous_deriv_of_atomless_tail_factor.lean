-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuous_deriv_of_atomless_tail_factor
-- name    : AvramDividend.Classical.continuous_deriv_of_atomless_tail_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T14:49:14.85198+00:00
-- url     : https://prove2.me/theorems/1511abb2-f62a-4a0c-8921-a6a34b27a9fc
-- title:
--   Derivative continuity from an atomless finite-tail factorisation
-- statement:
--   If W is continuous on the positive half-line and its derivative there factors as W(x) times the finite upper-tail mass of an atomless measure, then W' is continuous on the positive half-line. This is the deterministic calculus/measure step in the excursion-height proof of C1 scale-function regularity.
-- source:
--   Immediate from Proved continuous_measureReal_Ici_of_finite_noAtoms and continuity of products.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Ici_of_finite_noAtoms
open MeasureTheory Set

theorem AvramDividend.Classical.continuous_deriv_of_atomless_tail_factor
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤)
    (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x → deriv W x = W x * μ.real (Ici x)) :
    ContinuousOn (deriv W) (Ioi 0) := by sorry

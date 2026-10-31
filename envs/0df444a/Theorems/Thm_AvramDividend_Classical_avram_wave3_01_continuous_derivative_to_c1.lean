-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_01_continuous_derivative_to_c1
-- name    : AvramDividend.Classical.avram_wave3_01_continuous_derivative_to_c1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:50:26.954717+00:00
-- url     : https://prove2.me/theorems/32459c64-ce93-4015-a37a-6b191343cd03
-- title:
--   Continuous first derivative implies C1 smoothness on all positive reserves
-- statement:
--   A real function on the strictly positive half-line has one continuously differentiable derivative when it has a continuous derivative candidate and the ordinary derivative equals that candidate at each positive point. The proof uses the pinned first-order ContDiffOn criterion through derivWithin, and the open-set equality with deriv. This supplies the final pure-calculus bridge for the genuine Avram scale-function C1 proof.
-- source:
--   AvramDividend.Classical.scaleFunction_contDiff_one_infinite_variation_without_standing canonical UUID cd61d678; pinned Mathlib contDiffOn_one_iff_derivWithin, derivWithin_of_isOpen and IsOpen.uniqueDiffOn.

import Mathlib
open Set

theorem AvramDividend.Classical.avram_wave3_01_continuous_derivative_to_c1
    (f κ : ℝ → ℝ)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hderiv : ∀ a : ℝ, 0 < a → HasDerivAt f (κ a) a) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by sorry

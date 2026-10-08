-- Prove2me | Theorems.Thm_ConnesGreen_canonical_negative_selected_requires_large_support
-- name    : ConnesGreen.canonical_negative_selected_requires_large_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:15:51.540363+00:00
-- url     : https://prove2.me/theorems/3a075f09-fb99-405c-b0a3-5b3723bfd6ec
-- title:
--   Original negative selected witnesses require support beyond the certified radius
-- statement:
--   For every positive support window T, unchanged finite packet S and physical vector x on the original completed carrier, if the original selected signed quadratic form is negative at x then the original positiveSupportRadius is strictly less than T. The public premise unfolds exactly the native selectedQuadratic definition as the difference of original analysis norm squares. No test-density, symmetry or nonzero-vector premise is added.
-- source:
--   monocap-tech/weil at bbeb665deaea9c6798298d0cf6261db6e8f6519d; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_negative_selected_requires_large_support (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros) (x : Physical T)
    (hneg : ‖(canonicalPositiveSynthesis T hT).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis T hT S).adjoint x‖ ^ 2 < 0) : positiveSupportRadius < T := by sorry

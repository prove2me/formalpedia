-- Prove2me | Theorems.Thm_ConnesGreen_canonical_selected_covariance_le_small_support
-- name    : ConnesGreen.canonical_selected_covariance_le_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:55:57.973746+00:00
-- url     : https://prove2.me/theorems/3c9dd8d7-828e-48f7-b04f-3b70f50c4ffe
-- title:
--   Every unchanged selected packet inherits the small-support covariance bound
-- statement:
--   For 0<T<=the original positiveSupportRadius and every finite packet S of actual zeta zeros, its original negative selected covariance is at most the original full positive covariance on the same completed carrier. The complementary negative covariance is retained and is positive.
-- source:
--   monocap-tech/weil at 28829dbeeee2ba23d6c0f3cedaf22952174099c2; unchanged exact SmallSupportPositivity.lean declarations.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_selected_covariance_le_small_support (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros) :
    canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint ≤
      canonicalPositiveCovariance T hT := by sorry

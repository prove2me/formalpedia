-- Prove2me | Theorems.Thm_ConnesGreen_canonical_total_covariance_le_small_support
-- name    : ConnesGreen.canonical_total_covariance_le_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T04:55:59.58901+00:00
-- url     : https://prove2.me/theorems/9f020b10-1234-4d33-b2b8-81148386c1b0
-- title:
--   Full original negative covariance is bounded on the explicit small-support interval
-- statement:
--   For 0<T<=the original positiveSupportRadius, the complete negative covariance is at most the original positive covariance on the original completed physical carrier. All actual zeta-zero columns are retained. This follows from the accepted full original small-support Weil positivity and dense original tests.
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

theorem ConnesGreen.canonical_total_covariance_le_small_support (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) :
    canonicalNegativeSynthesis T hT ∘L (canonicalNegativeSynthesis T hT).adjoint ≤
      canonicalPositiveCovariance T hT := by sorry

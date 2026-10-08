-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_small_support
-- name    : ConnesGreen.canonical_endpoint_half_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:17:05.103965+00:00
-- url     : https://prove2.me/theorems/fffbef4f-642c-43b4-b243-f28571437040
-- title:
--   Original ordered support-right endpoint has its half-bound inside the explicit interval
-- statement:
--   Let R be the original positiveSupportRadius. For every endpoint c with 0<=c<R and every finite packet S of actual zeta zeros, the original support-right marker is at least one half the identity on its unchanged coefficient space. Positive regularization tends to zero first, then the support window tends to c from the right. This concerns the explicit interior interval and does not identify the intended critical endpoint.
-- source:
--   monocap-tech/weil at bbeb665deaea9c6798298d0cf6261db6e8f6519d; WeilDefect/Connes/SmallSupportPositivity.lean. Original native declarations and exact constant definition bodies unchanged.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_small_support (c : ℝ) (hc : 0 ≤ c)
    (hcr : c < positiveSupportRadius) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S := by sorry

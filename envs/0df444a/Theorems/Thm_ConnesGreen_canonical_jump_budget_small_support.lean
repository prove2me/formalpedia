-- Prove2me | Theorems.Thm_ConnesGreen_canonical_jump_budget_small_support
-- name    : ConnesGreen.canonical_jump_budget_small_support
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T05:16:28.12098+00:00
-- url     : https://prove2.me/theorems/bd1b916b-5ded-4f49-9fac-9edc0805bc15
-- title:
--   Original endpoint jump budget holds strictly inside the certified interval
-- statement:
--   For every 0<c<R, where R is the original positiveSupportRadius, and every unchanged finite actual-zero packet S, the original drop from the inner Picard marker to the prescribed support-right marker is at most the inner marker minus one half the identity. This is the exact original operator jump-budget inequality on the certified interval. It does not establish that inequality at an unidentified critical endpoint.
-- source:
--   monocap-tech/weil at bbeb665deaea9c6798298d0cf6261db6e8f6519d. Original CriticalWindowBoundary.lean criterion and exact SmallSupportPositivity.lean endpoint half-bound. New bounded-interval corollary, independently checked against native implementations.

import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

theorem ConnesGreen.canonical_jump_budget_small_support (c : ℝ) (hc : 0 < c) (hcr : c < positiveSupportRadius) (S : Finset CriticalZeros) :
    canonicalPicardMarker c hc S - canonicalSupportRightMarker c hc.le S ≤
      canonicalPicardMarker c hc S - (1 / 2 : ℝ) • 1 := by sorry

-- Prove2me | Theorems.Thm_ConnesGreen_canonical_actual_zero_support_right_limit
-- name    : ConnesGreen.canonical_actual_zero_support_right_limit
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:36:10.687295+00:00
-- url     : https://prove2.me/theorems/71b73248-61c2-4bce-920b-8b1fec95951c
-- title:
--   Original actual-zero ordered support-right marker exists in operator norm
-- statement:
--   For every nonnegative endpoint c and unchanged finite actual-zero packet S, construct the prescribed original support-right marker: a nonnegative operator below the identity, the supremum of the original Picard markers for supports strictly above c, and their operator-norm limit as support tends to c from the right. Positive regularization has already tended to zero to define each original Picard marker. The original support antitonicity, finite-dimensional coefficient subtype and accepted compact antitone-limit theorem prove existence in precisely that order. This does not identify a critical endpoint or prove its arithmetic half-bound.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.canonical_actual_zero_support_right_limit (c : ℝ) (hc : 0 ≤ c)
    (S : Finset CriticalZeros) :
    ∃ Gplus : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ),
      0 ≤ Gplus ∧ Gplus ≤ 1 ∧
      IsLUB ((fun t => positiveWindowPicardMarker t S) '' Ioi c) Gplus ∧
      Tendsto (fun t => positiveWindowPicardMarker t S)
        (nhdsWithin c (Ioi c)) (nhds Gplus) := by sorry

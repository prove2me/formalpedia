-- Prove2me | Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
-- name    : ConnesGreen.canonicalPicardMarker_window_antitone
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:38:18.805715+00:00
-- url     : https://prove2.me/theorems/c6cb1ee0-ebb7-461c-bbf9-df97526382de
-- title:
--   Original Picard markers retain support-window order
-- statement:
--   The original positive-regularization norm limits preserve support-window order: on nested positive original windows, the larger original Picard marker is below the smaller one. The original inner limits are already constructed, and the accepted original regularized marker comparison passes to their norm limits. No support-right limit, arithmetic positivity or RH is assumed.
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

theorem ConnesGreen.canonicalPicardMarker_window_antitone (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) :
    canonicalPicardMarker T hT S ≤ canonicalPicardMarker t ht S := by sorry

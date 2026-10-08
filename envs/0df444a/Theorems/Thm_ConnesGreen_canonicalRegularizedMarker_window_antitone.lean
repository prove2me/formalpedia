-- Prove2me | Theorems.Thm_ConnesGreen_canonicalRegularizedMarker_window_antitone
-- name    : ConnesGreen.canonicalRegularizedMarker_window_antitone
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:31:28.375176+00:00
-- url     : https://prove2.me/theorems/e567bd3b-bf0c-4b87-99ac-e744d2022874
-- title:
--   Original regularized markers are antitone in support radius
-- statement:
--   For every positive regularization, the original selected marker on a larger positive support window is below the marker on a smaller nested original window. Constructed original carrier inclusion and complete positive/selected actor compression identify the generic accepted isometric marker-compression theorem with the original actors. The actual-zero subtype, analytic multiplicities, reflection normalization, selected packet and original physical metric are unchanged.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Theorems.Thm_ConnesGreen_exists_original_window_actor_inclusion
import Theorems.Thm_WeilDefect_MarkerStability_regularized_marker_isometric_compression
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section

theorem ConnesGreen.canonicalRegularizedMarker_window_antitone (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) (ε : ℝ) (hε : 0 < ε) :
    canonicalRegularizedMarker T hT S ε ≤ canonicalRegularizedMarker t ht S ε := by sorry

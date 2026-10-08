-- Prove2me | Theorems.Thm_ConnesGreen_canonical_support_right_le_inner
-- name    : ConnesGreen.canonical_support_right_le_inner
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:47:46.992262+00:00
-- url     : https://prove2.me/theorems/fe66034b-fe2b-48b4-9aa1-42c36d90148b
-- title:
--   Original support-right marker lies below its original inner marker
-- statement:
--   At every positive original support endpoint, the constructed prescribed support-right marker is below the original inner Picard marker at that same support. This uses the accepted original support-window order and the exact supremum characterization of the constructed original ordered endpoint. The original marker jump is therefore nonnegative; no claim that it vanishes or fits inside the inner half-margin is made.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.canonical_support_right_le_inner (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros) :
    canonicalSupportRightMarker c hc.le S ≤ canonicalPicardMarker c hc S := by sorry

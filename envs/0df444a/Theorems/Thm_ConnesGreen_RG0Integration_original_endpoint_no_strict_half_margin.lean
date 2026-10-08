-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_original_endpoint_no_strict_half_margin
-- name    : ConnesGreen.RG0Integration.original_endpoint_no_strict_half_margin
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:47:27.161481+00:00
-- url     : https://prove2.me/theorems/309814af-30e7-4195-a202-ecc243f37255
-- title:
--   Constructed original ordered endpoint has no strict half margin under larger-window failure
-- statement:
--   For a positive original support endpoint c and unchanged actual-zero packet, suppose every larger original window fails the inner Picard half-bound. Then the CONSTRUCTED original prescribed support-right marker admits no scalar lower bound aI for any a>1/2. Its norm-limit existence is now proved and is not a hypothesis. The earlier accepted boundary implication is specialized using the exact constructed original endpoint specification. Larger-window failure remains explicit; the endpoint half-bound, critical-endpoint identification, unconditional neutral attainment and RH are not established.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_outer_no_strict_half_margin
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.RG0Integration.original_endpoint_no_strict_half_margin
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (hbad : ∀ T : ℝ, ∀ hT : 0 < T, c < T →
      ¬ (1/2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (a : ℝ) (ha : (1/2 : ℝ) < a) :
    ¬ a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc.le S := by sorry

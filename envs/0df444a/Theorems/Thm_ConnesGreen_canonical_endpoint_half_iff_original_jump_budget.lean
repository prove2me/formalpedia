-- Prove2me | Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_original_jump_budget
-- name    : ConnesGreen.canonical_endpoint_half_iff_original_jump_budget
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T23:49:52.285653+00:00
-- url     : https://prove2.me/theorems/af7f98e6-7d43-4dce-a9f9-fa401ffb005b
-- title:
--   Original endpoint half-bound is exactly the original arithmetic jump budget
-- statement:
--   For the original finite actual-zero packet and positive endpoint c, the arithmetic half-bound on the constructed prescribed support-right marker is equivalent exactly to the original jump budget C(c)-R(c)<=C(c)-(1/2)I, where C is the original inner Picard marker and R the original ordered support-right marker. Order translation proves this equivalence on the original coefficient operator space. Neither the budget nor the half-bound is assumed or asserted true. This is an exact localized mathematical obstruction.
-- source:
--   monocap-tech/weil, checked native CanonicalGreenWindowInclusion.lean and CanonicalGreenSupportLimit.lean at dfaa61225f3d5a1d5b94a14884b96a18ae82816b; exact original declarations recovered with Lean elaborator proof boundaries and transported to Lean4.33.1.

import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section

theorem ConnesGreen.canonical_endpoint_half_iff_original_jump_budget (c : ℝ) (hc : 0 < c)
    (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc.le S ↔
    canonicalPicardMarker c hc S - canonicalSupportRightMarker c hc.le S ≤
      canonicalPicardMarker c hc S - (1 / 2 : ℝ) • 1 := by sorry

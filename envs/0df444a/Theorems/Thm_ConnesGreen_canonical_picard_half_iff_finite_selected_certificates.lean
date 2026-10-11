-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_selected_certificates
-- name    : ConnesGreen.canonical_picard_half_iff_finite_selected_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T22:24:33.901074+00:00
-- url     : https://prove2.me/theorems/c73d6d16-ea2f-4177-bee8-6604c46af5bb
-- title:
--   Original inner half-bound has exact finite certificates on its selected coefficient space
-- statement:
--   At one fixed positive original support window t and unchanged selected actual-zero packet S, the original inner Picard marker is at least half the identity exactly when, for every positive accuracy δ, some finite reflection-closed actual-zero packet F containing S has COMPLETE omitted positive-column norm-square tail less than δ and nonnegative selected coefficient correction δI−N*N+C*B⁻¹C. Here P_F synthesizes exactly the original positive F columns, N is the ORIGINAL selected negative synthesis for S, B=P_F*P_F+δI and C=P_F*N. The correction acts only on the original selected S coefficient space; the sole inverse is on the finite positive F coefficient space and is guaranteed by positive δ. The same window, packets, δ and complete tail allowance are retained. This is an exact alternative to the larger tagged Gram PSD certificate, not a proof of the correction inequality, larger-window extension or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/FiniteGram.lean and WeilDefect/Connes/FiniteSelectedCertificates.lean at compiling source head d28908eb3d61a4a81d7b4a5aff70ea26b6680897
--
--   Literature/source audit addendum (COR-22): The exact native finite-selected-certificate equivalence was independently checked in Lean. Positive-column tail summability supplies a finite cutoff, but does not by itself prove nonnegativity of the selected correction. The same positive regularization parameter is retained in the tail tolerance and selected correction. Arithmetic transfer checkpoint: monocap-tech/provenance 178c83225b2300506ff622899d08ec3c987137d5, rh/checkpoints/RH_ZERO_PROV_2_EULER_WEIL_MARKER_TRANSFER_20260920.md, SHA256 0bb48b950f09220f7b2f193c16b45b15add0333906f919f8b50ca915f77a1a0d. Exact checkpoint bytes were verified in retained local Git; public availability has not been checked.

import Definitions.Def_ConnesGreen_finite_selected_correction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open ContinuousLinearMap

theorem ConnesGreen.canonical_picard_half_iff_finite_selected_certificates
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      0 ≤ canonicalFiniteSelectedCorrection t ht S F δ := by sorry

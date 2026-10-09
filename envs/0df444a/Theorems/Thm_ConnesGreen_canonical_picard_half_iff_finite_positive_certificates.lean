-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_positive_certificates
-- name    : ConnesGreen.canonical_picard_half_iff_finite_positive_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T20:31:56.322579+00:00
-- url     : https://prove2.me/theorems/54eae90e-adf9-4e4b-b8e1-ab3ce2431d56
-- title:
--   Original inner half-bound is equivalent to finite positive certificates at a fixed window
-- statement:
--   At ONE FIXED positive original support window and unchanged selected actual-zero packet S, the inner Picard marker is at least one half of the identity exactly when, for every positive error allowance δ, there exists a finite reflection-closed actual-zero packet F containing S with omitted positive-column norm-square sum less than δ such that EVERY original physical vector has selected negative analysis energy at most its finite positive analysis energy on F plus δ times its squared norm. The packet is chosen after δ and before all physical vectors. The support radius is fixed before accuracy varies; it cannot approach an endpoint as accuracy improves. This is an exact finite arithmetic target for the unchanged complete positive synthesis and selected negative synthesis. It does not prove the finite inequalities, any larger-window extension, or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FinitePositiveCertificates.lean at compiling source head 14549ed6d5274193f7f209b0f0690f6aa67f579d. Original actual zeta zeros, multiplicities, carrier, complete positive synthesis and selected negative actor preserved.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

theorem ConnesGreen.canonical_picard_half_iff_finite_positive_certificates
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      ∀ x : Physical t, ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 ≤
        (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) +
          δ * ‖x‖ ^ 2 := by sorry

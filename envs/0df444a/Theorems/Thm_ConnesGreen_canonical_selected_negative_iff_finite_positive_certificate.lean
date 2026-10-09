-- Prove2me | Theorems.Thm_ConnesGreen_canonical_selected_negative_iff_finite_positive_certificate
-- name    : ConnesGreen.canonical_selected_negative_iff_finite_positive_certificate
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T20:29:54.588993+00:00
-- url     : https://prove2.me/theorems/02423a93-ff54-43b8-9247-b9858312def4
-- title:
--   Original selected negativity has a finite positive-packet certificate with tail error
-- statement:
--   For any positive original support window, unchanged finite selected actual-zero packet S and physical vector x, the COMPLETE positive-minus-selected-negative energy is negative exactly when there exist a positive error allowance δ and a finite reflection-closed actual-zero packet F containing S with positive-column energy tail less than δ such that the finite positive analysis energy on F minus the ORIGINAL selected negative analysis energy, plus δ times the squared physical norm of x, is strictly negative. The selected negative actor is not enlarged to F. The complete actual positive tail is paid explicitly; negativity of a truncated positive form alone is not enough. Actual zeta zeros, analytic multiplicities, pair normalization and physical carrier are unchanged. This equivalence supplies a certified finite witness format, not an unconditional negativity or RH claim.
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

theorem ConnesGreen.canonical_selected_negative_iff_finite_positive_certificate
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (x : Physical t) :
    ‖(canonicalPositiveSynthesis t ht).adjoint x‖ ^ 2 -
      ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 < 0 ↔
    ∃ δ : ℝ, 0 < δ ∧ ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      (∑ ρ ∈ F, ‖⟪positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, x⟫_ℂ‖ ^ 2) -
        ‖(canonicalSelectedSynthesis t ht S).adjoint x‖ ^ 2 + δ * ‖x‖ ^ 2 < 0 := by sorry

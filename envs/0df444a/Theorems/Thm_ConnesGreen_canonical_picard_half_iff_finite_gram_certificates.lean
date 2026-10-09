-- Prove2me | Theorems.Thm_ConnesGreen_canonical_picard_half_iff_finite_gram_certificates
-- name    : ConnesGreen.canonical_picard_half_iff_finite_gram_certificates
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-08T21:10:52.066617+00:00
-- url     : https://prove2.me/theorems/af58aac3-8687-407e-874f-8dc98f4ee406
-- title:
--   Original inner half-bound is equivalent to finite Gram PSD certificates at a fixed window
-- statement:
--   At one fixed positive support window t and unchanged finite selected actual-zero packet S, the original inner Picard marker is at least half the identity exactly when for every positive accuracy δ there exists a finite reflection-closed packet F containing S with COMPLETE omitted positive-column norm-square sum less than δ and positive semidefinite finite certificate Gram matrix. The matrix is formed from the original positive F columns and original selected negative S columns on the original physical carrier, using D = δI + positive finite covariance minus selected negative covariance. F is chosen after δ and before all vectors; t stays fixed. This is an exact arithmetic target, not a proof of matrix positivity, larger-window extension, or RH.
-- source:
--   monocap-tech/weil, WeilDefect/Screening/FiniteGram.lean and WeilDefect/Connes/FiniteCertificateGram.lean at compiling source head df7cd5371e1778aa18f13856f32247a971f62d6b

import Definitions.Def_ConnesGreen_finite_certificate_gram
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem ConnesGreen.canonical_picard_half_iff_finite_gram_certificates
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) ↔
    ∀ δ : ℝ, 0 < δ → ∃ F : Finset CriticalZeros,
      S ⊆ F ∧ (∀ ρ ∈ F, reflectedZero ρ ∈ F) ∧
      (∑' ρ : {ρ : CriticalZeros // ρ ∉ F},
        ‖positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1‖ ^ 2) < δ ∧
      (canonicalFiniteCertificateGram t S F δ).PosSemidef := by sorry

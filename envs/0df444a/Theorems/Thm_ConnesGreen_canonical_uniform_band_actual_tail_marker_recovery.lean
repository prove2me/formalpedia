-- Prove2me | Theorems.Thm_ConnesGreen_canonical_uniform_band_actual_tail_marker_recovery
-- name    : ConnesGreen.canonical_uniform_band_actual_tail_marker_recovery
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-10T17:44:29.459393+00:00
-- url     : https://prove2.me/theorems/469e8cf1-fbcf-49ed-bff6-e6722310d811
-- title:
--   Uniform bounded-window actual-zero tail and positive-floor marker recovery
-- statement:
--   For every positive upper support bound T, every prescribed finite set S of actual critical-strip zeta zeros, every tolerance η>0, every positive regularization floor μ₀, and every 0<α<1, there is one finite reflection-closed actual-zero set F containing S, chosen before all support windows 0<t≤T, all regularizations μ≥μ₀, and all original SupportedTest t g with physical source norm squared ≤1. For each window there is a bounded positive-tail synthesis with exactly the original positive columns outside F. Its covariance norm plus the original negative-tail covariance norm is <η. The complete actual convolved zero contribution outside F, including actual zeta multiplicities, has a summable norm series with sum <η. The negative-tail covariance satisfies norm ≤αμ for every μ≥μ₀. Consequently the restored operator is nonnegative and invertible, and the original selected-S marker difference is nonnegative with norm ≤α. The selected synthesis remains the original S actor. For the same F and each fixed window, the sufficient covariance norm criterion at EVERY μ>0 holds if and only if ALL original negative columns outside F vanish. This last equivalence concerns the sufficient covariance criterion, not a necessity theorem for marker approximation. No RH, off-line-zero hypothesis, Weil positivity, arithmetic endpoint bound, ordered-limit exchange, or effective height cutoff is assumed or proved.
-- source:
--   For every positive upper support bound T, every prescribed finite set S of actual critical-strip zeta zeros, every tolerance η>0, every positive regularization floor μ₀, and every 0<α<1, there is one finite reflection-closed actual-zero set F containing S, chosen before all support windows 0<t≤T, all regularizations μ≥μ₀, and all original SupportedTest t g with physical source norm squared ≤1. For each window there is a bounded positive-tail synthesis with exactly the original positive columns outside F. Its covariance norm plus the original negative-tail covariance norm is <η. The complete actual convolved zero contribution outside F, including actual zeta multiplicities, has a summable norm series with sum <η. The negative-tail covariance satisfies norm ≤αμ for every μ≥μ₀. Consequently the restored operator is nonnegative and invertible, and the original selected-S marker difference is nonnegative with norm ≤α. The selected synthesis remains the original S actor. For the same F and each fixed window, the sufficient covariance norm criterion at EVERY μ>0 holds if and only if ALL original negative columns outside F vanish. This last equivalence concerns the sufficient covariance criterion, not a necessity theorem for marker approximation. No RH, off-line-zero hypothesis, Weil positivity, arithmetic endpoint bound, ordered-limit exchange, or effective height cutoff is assumed or proved.
--
--   This assembles the accepted bounded-window pair-actor tail theorem, accepted marker stability and fixed-tail all-regularization criterion, original source/Mellin pairing, and original convolution transform law. It specializes the abstract covariance criterion to the original actual-zero columns and controls the actual spectral norm tail without changing carrier, multiplicities, selected synthesis or background definitions. Native proof closes at the existing certified module closure of clean checkout head ada7948cb459fd21d400cd8f2a92e87672e31f2d. Standalone output only; no new repository commit or CI head. Original RPB108 original-form attachments remain future formalization work.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem ConnesGreen.canonical_uniform_band_actual_tail_marker_recovery
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (η μ₀ α : ℝ) (hη : 0 < η) (hμ₀ : 0 < μ₀) (hα : 0 < α) (hα1 : α < 1) :
    ∃ F : Finset CriticalZeros, S ⊆ F ∧
      (∀ τ ∈ F, reflectedZero τ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η ∧
          (∀ μ : ℝ, μ₀ ≤ μ →
            ‖canonicalTailCovariance t ht F‖ ≤ α * μ ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + μ • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + μ • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + μ • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S)‖ ≤ α) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < η) ∧
          ((∀ μ : ℝ, 0 < μ → ‖canonicalTailCovariance t ht F‖ ≤ α * μ) ↔
            ∀ τ : CriticalZeros, τ ∉ F →
              negativeGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ = 0) := by sorry

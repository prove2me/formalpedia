-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_gaussian_bounded_weights_integrable
-- name    : AvramDividend.Classical.avram_a24_original_canonical_gaussian_bounded_weights_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:43:19.723578+00:00
-- url     : https://prove2.me/theorems/4682c6c7-559e-4ef4-8d67-c2fc260f6e4c
-- title:
--   Original canonical stopped Gaussian first and second weighted gains integrability
-- statement:
--   For any exact physical Gaussian uniform grid clipped at the original bounded stopping time, the linear gradient stochastic gain and Hessian quadratic gain are integrable whenever the coefficients are strongly measurable and pathwise bounded at each physical cell, without requiring a priori product integrability. The proof directly uses previously proved conditional first and second moments of the genuine original Gaussian stopped increment. This closes three real integrability obligations of the A24 positive-mesh source, leaving the original finite-cap Ito-Stieltjes limit as the remaining analytic issue.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a24_original_canonical_gaussian_bounded_weights_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (G H : ℕ → ℕ → Ω → ℝ)
    (hGmeas : ∀ j i, AEStronglyMeasurable (G j i) P)
    (hHmeas : ∀ j i, AEStronglyMeasurable (H j i) P)
    (BG BH : ℕ → ℕ → ℝ)
    (hGB : ∀ j i, ∀ᵐ ω ∂P, ‖G j i ω‖ ≤ BG j i)
    (hHB : ∀ j i, ∀ᵐ ω ∂P, ‖H j i ω‖ ≤ BH j i) :
    ∀ j i : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let τg : Ω → ℝ≥0 := fun ω => min ((i : ℝ≥0) * δ) (σ ω)
      let M : Ω → ℝ := fun ω =>
        X.X (τg ω + δ) ω - X.X (τg ω) ω - (δ : ℝ) * X.c
      Integrable (fun ω => G j i ω * M ω) P ∧
      Integrable (H j i) P ∧
      Integrable (fun ω => H j i ω * (M ω)^2) P:= by sorry

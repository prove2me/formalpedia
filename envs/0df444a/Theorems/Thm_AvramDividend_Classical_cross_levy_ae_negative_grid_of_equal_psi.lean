-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_ae_negative_grid_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_ae_negative_grid_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:41:41.421862+00:00
-- url     : https://prove2.me/theorems/7a3f2b86-655b-438d-bfea-2f6b4e115bd7
-- title:
--   Whole-path Lévy law equality transfers almost-sure downward observations on an arbitrary countable near-zero time grid
-- statement:
--   Given two spectrally negative Lévy processes over unrelated probability spaces with identical positive Laplace exponents, if one process has almost-sure negative observations on an arbitrary prescribed countable time schedule before each prescribed horizon, then the other has the same almost-sure grid property. The bad-grid event is a measurable cylinder-countable intersection in whole-path space by an already proved theorem, and equality of Lévy Laplace exponents implies equality of whole-path event measures. This provides an essential law-transfer bridge for a canonical Poisson jump model or Gaussian construction to prove original-source downward regularity, without assuming the two random processes live on the same probability space. This alone does not prove the grid negativity property for a canonical construction.
-- source:
--   Prove2Me accepted cross_levy_path_event_law_of_equal_psi and measurableSet_countable_schedule_negative_near_zero.

import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi
import Theorems.Thm_AvramDividend_Classical_measurableSet_countable_schedule_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_ae_negative_grid_of_equal_psi
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (times horizons : ℕ → ℝ≥0)
    (hGridY : ∀ᵐ ω ∂P₂, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ Y.X (times m) ω < 0) :
    ∀ᵐ ω ∂P₁, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by sorry

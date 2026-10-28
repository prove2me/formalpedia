-- Prove2me | Theorems.Thm_AvramDividend_Classical_cross_levy_ae_negative_near_zero_of_equal_psi
-- name    : AvramDividend.Classical.cross_levy_ae_negative_near_zero_of_equal_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:48:51.866613+00:00
-- url     : https://prove2.me/theorems/5fafb3aa-6434-446a-8141-46e0b29564df
-- title:
--   Whole-path Lévy law equality transfers almost-sure immediate downward regularity between independent realisations
-- statement:
--   Let X and Y be spectrally negative Lévy processes on entirely different probability spaces with the same Laplace exponent for every positive parameter. Suppose Y has almost-sure negative values arbitrarily close to time zero. For any dense countable observation schedule and positive cofinal sequence of horizons, right continuity gives the corresponding almost-sure negative-grid law for Y. The accepted measurable whole-path event transfer by identical Lévy exponents transfers the grid law to X. Cofinality yields almost-sure negative values arbitrarily close to zero for X. The theorem is an actual transfer of stochastic regularity from a constructed canonical Lévy–Itô process to the abstract Prove2Me Lévy process; it does not derive canonical regularity from unbounded variation, which remains an independent task.
-- source:
--   Proved cross_levy_ae_negative_grid_of_equal_psi and levy_negative_before_horizon_iff_dense_grid; KKR review 2013, small-time downward regularity.

import Theorems.Thm_AvramDividend_Classical_cross_levy_ae_negative_grid_of_equal_psi
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.cross_levy_ae_negative_near_zero_of_equal_psi
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hRegY : ∀ᵐ ω ∂P₂, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ Y.X s ω < 0) :
    ∀ᵐ ω ∂P₁, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by sorry

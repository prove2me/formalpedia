-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:57:43.200313+00:00
-- url     : https://prove2.me/theorems/e72ddf78-9dfe-4a4f-8afd-db94777a13cb
-- title:
--   Original Lévy finite-grid full Stieltjes ENNReal expected cash budget
-- statement:
--   For an actual spectrally negative Lévy source and any nondecreasing adapted left-continuous strategy, the nonnegative Lebesgue integral of entire Stieltjes cell cash weighted by the original exponential source martingale is at most the ENNReal conversion of initial expected postpayment wealth. This is the integrable ENNReal companion of the original real stochastic budget, suitable for Fatou and diffuse/singular dividend measure passage.
-- source:
--   Genuine source finite-grid real expected budget 3397f585 and true L1 integrability 668c8640, Mathlib ofReal_integral_eq_lintegral_ofReal

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) ≤
    ENNReal.ofReal (∫ ω,
      Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry

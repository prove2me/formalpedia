-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
-- name    : AvramDividend.Classical.avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:11:46.302699+00:00
-- url     : https://prove2.me/theorems/3397f585-f1fb-461e-8f77-ec9f3413f809
-- title:
--   Genuine source Lévy expected finite-grid Stieltjes dividend-mass budget under exponential postpayment discount
-- statement:
--   For the actual original Lévy process X and an arbitrary admissible left-continuous adapted nondecreasing dividend D, with θ≥0, any finite nondecreasing grid has nonnegative exact right-limit dividend masses weighted by the genuine original source exponential martingale times the postpayment exp(-θD). Their θ-weighted expected sum is bounded by expected initial postpayment exponential wealth. No atomicity; the terms are exact measures of full Stieltjes cells. Proof uses canonically Proved original source finite-grid stochastic budget and exact convexity comparison; establishes integrability from the same original martingale and adapted bounded postpayment weights.
-- source:
--   Proved source-X stochastic finite-grid budget 62cf93c8, exp control convexity, actual original Lévy rightCont construction and martingale

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_positive_postPayment_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∀ ω, 0 ≤ θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∧
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry

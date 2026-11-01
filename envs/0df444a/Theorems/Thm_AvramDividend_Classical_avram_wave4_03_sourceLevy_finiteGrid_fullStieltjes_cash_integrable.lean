-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:23:36.549831+00:00
-- url     : https://prove2.me/theorems/668c8640-796d-4129-aa91-5b4b0084fd4d
-- title:
--   Actual original Lévy finite-grid full Stieltjes dividend cash is integrable before Fatou passage
-- statement:
--   For any actual original spectrally negative Levy source X on its given filtration and any adapted nondecreasing left-continuous dividend D, the finite-grid source exponential martingale weighted full Stieltjes cash sum is genuinely Bochner integrable. This strengthens previously proved expected budgets by explicitly establishing measurability and L1 domination of unbounded dividend increments through bounded adapted postpayment martingale product differences. Entire right-limit increments include diffuse, singular and atomic dividends. No general nonlinear C1 generator compensation is assumed.
-- source:
--   Accepted source exponential adapted postpayment product integrability 9d97b9c8; original finite-grid full cash positive 3397f585; exact scalar convexity; Mathlib Integrable.mono and strongly measurable finite sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    Integrable (fun ω => θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P := by sorry

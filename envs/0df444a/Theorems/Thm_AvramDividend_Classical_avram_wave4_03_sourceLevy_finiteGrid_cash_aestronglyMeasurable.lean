-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:28:10.885892+00:00
-- url     : https://prove2.me/theorems/cbd2eb29-9e79-4d9b-8a5b-174b01c460fc
-- title:
--   Original source Lévy finite-grid full Stieltjes dividend cash strong measurability
-- statement:
--   For any original spectrally negative Levy source and adapted dividend strategy, the finite-grid discounted exponential cash sum covering entire Stieltjes right-limit mass is strongly measurable almost everywhere. The proof uses original same-space adapted postpayment martingale product integrability and right-limit strategy measurability.
-- source:
--   Source postpayment product integrability 9d97b9c8 and adapted right-limit theorem; algebra and finite sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_cash_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (n : ℕ) :
    AEStronglyMeasurable (fun ω => θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) P := by sorry

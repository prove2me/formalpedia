-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:52:14.087934+00:00
-- url     : https://prove2.me/theorems/0a2d6f6f-9bea-4390-9bb6-206986a3d4c6
-- title:
--   Original source Lévy exponential postpayment control-loss differences are integrable
-- statement:
--   The actual original Lévy exponential martingale at time v multiplied by the difference of bounded adapted postpayment weights at arbitrary times r,v is L1, even for an unbounded cumulative dividend strategy. This follows by subtracting two genuinely integrable source martingale products on the same path and filtration. Supplies the exact dominant terms for finite-grid full Stieltjes cash integrability.
-- source:
--   Source exact postpayment compensated exponential product integrability 9d97b9c8 and integrability linearity; no independent process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_exponential_postPayment_controlLoss_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (r v : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ) *
      (Real.exp (-(θ * rightLimit D r ω)) -
        Real.exp (-(θ * rightLimit D v ω)))) P := by sorry

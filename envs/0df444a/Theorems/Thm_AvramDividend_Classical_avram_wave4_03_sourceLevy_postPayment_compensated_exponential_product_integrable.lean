-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:43:08.500019+00:00
-- url     : https://prove2.me/theorems/9d97b9c8-39a6-4d86-89a9-f4b6165d9791
-- title:
--   Original same-filtration Lévy exponential martingale times adapted postpayment discount is integrable at arbitrary times
-- statement:
--   For the genuinely original source Lévy process and any adapted nondecreasing left-continuous dividend strategy, every compensated source exponential at deterministic v multiplied by the true same-path postpayment discount at r is integrable under the original probability measure. The argument invokes the source exponential martingale, adapted right limits and boundedness of the discounted factor.
-- source:
--   Source Lévy right-continuous process, canonically Proved compensated exponential martingale, adapted postpayment rightLimit and dividendStrategy_le_rightLimit; extracted from the accepted source finite-grid stochastic budget proof 3397f585.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_postPayment_compensated_exponential_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (r v : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (-(θ * rightLimit D r ω)) *
      Real.exp (θ * X.X v ω - (v : ℝ) * X.ψ θ)) P := by sorry

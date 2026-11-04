-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_measurable
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:06:54.43646+00:00
-- url     : https://prove2.me/theorems/e0a94a17-0eb8-4a8f-a7d0-bc3695fc6268
-- title:
--   Original ruin-stopped strict open-horizon Stieltjes dividend cash is measurable
-- statement:
--   The genuine original stopped weighted Stieltjes cash strictly before a fixed real horizon is jointly measurable for every measurable ruin or other extended-valued random payment clock. It retains the time-zero right-payment and all other payments before T, excluding exactly the horizon atom. Uses the accepted original dividend-measure s-finite kernel and jointly measurable paymentTimes, without changing the underlying probability space.
-- source:
--   The accepted original source kernel measurable_random_indicator_lintegral, dividendMeasure_global_sfinite_kernel_exists, and paymentTimes_joint_measurable, specialised to Iio rather than Iic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (hσ : Measurable σ)
    (q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (σ ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry

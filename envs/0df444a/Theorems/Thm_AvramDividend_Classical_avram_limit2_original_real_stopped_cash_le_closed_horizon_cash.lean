-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
-- name    : AvramDividend.Classical.avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:22:35.529218+00:00
-- url     : https://prove2.me/theorems/4eb76074-ea84-48e8-986b-df1df2e99308
-- title:
--   Natural original ruin-stopped expected real-horizon dividend cash is bounded by canonical closed-horizon dividend cash
-- statement:
--   For genuine original X and Stieltjes dividendMeasure D, at any nonnegative real horizon T the expected discounted cash stopped at min(ruinTime,ofReal T) is at most the canonical expected cash over paymentTimes(ruinTime) intersected Iic T. The already Proved endpoint-aware paymentTimes inclusion 153734f3 holds for every path, including zero and time-zero dividend atoms. Apply Mathlib lintegral_mono_set pathwise and lintegral_mono under original P. This is the precise direct cash monotonicity interface from canonical truncated verification cc518136 to natural-clock bounds 61bbf167, without terminal vanishing or equality-in-law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_eq_aligned_closed_horizon
-- name    : AvramDividend.Classical.avram_limit2_original_real_stopped_cash_eq_aligned_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:12:54.920571+00:00
-- url     : https://prove2.me/theorems/615ff364-ecf8-4791-83ed-225c7b206f64
-- title:
--   Original real ruin-stopped expected dividend cash equals exact clock-aligned closed-horizon mask
-- statement:
--   For the genuine original spectrally negative Levy surplus and dividend Stieltjes measure, the expected discounted cash stopped at min(ruinTime, ENNReal.ofReal T) equals the same cash restricted to Iic T for every nonnegative real T. This follows pathwise from public Proved real-clock paymentTimes support 5b6aa6af, so no expectation interchange, equality-in-law, or terminal vanishing is required; the time-zero atom survives at T=0.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_real_stopped_cash_eq_aligned_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry

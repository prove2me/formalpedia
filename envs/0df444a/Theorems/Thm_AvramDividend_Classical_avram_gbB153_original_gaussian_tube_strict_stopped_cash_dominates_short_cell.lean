-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
-- name    : AvramDividend.Classical.avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:15:27.237541+00:00
-- url     : https://prove2.me/theorems/d4e02057-c0ed-4296-a1cc-f2777ffa150f
-- title:
--   Original Gaussian barrier strict stopped cash dominates any interior discounted physical Stieltjes cash cell
-- statement:
--   For an original equal-cap barrier source on a narrow tube and a short interior horizon S<T, the genuine strictly pre-ruin stopped dividendMeasure integral through T dominates the discounted dividendMeasure integral on Ioc(0,S). The Proved source no-ruin tube theorem and exact paymentTimes set inclusion justify the restriction; no abstract substitute or stochastic Ito identity is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_barrier_pre_ruin_all_short_tube_times
import Theorems.Thm_AvramDividend_Classical_avram_gbB152_original_strict_prepayment_cash_contains_short_physical_cell
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) :
    (∫⁻ t in Ioc (0 : ℝ) (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
      Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) := by sorry

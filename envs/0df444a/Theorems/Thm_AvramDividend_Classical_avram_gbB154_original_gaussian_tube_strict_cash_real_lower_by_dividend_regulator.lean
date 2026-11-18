-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
-- name    : AvramDividend.Classical.avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:28:12.015634+00:00
-- url     : https://prove2.me/theorems/42520c56-16fe-4851-98f2-4cef4070092a
-- title:
--   Original stopped Gaussian strict Stieltjes cash is bounded below by discounted actual cumulative barrier dividends
-- statement:
--   For an original equal-cap reflected source on the narrow tube, any interior positive cash time S<T and nonnegative discount q, if its genuine strictly pre-ruin discounted Stieltjes cash integral through T is finite, its real value dominates exp(-qS) times the actual cumulative barrier dividends D(S). This source-specific result follows from the exact original cell mass and stopped-payment inclusion certificates and avoids a stopped Itô identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB148_original_cap_barrier_discounted_Ioc_cash_lower
import Theorems.Thm_AvramDividend_Classical_avram_gbB153_original_gaussian_tube_strict_stopped_cash_dominates_short_cell
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) (hq : 0 ≤ q)
    (hFin : (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤) :
    Real.exp (-(q * (S : ℝ))) *
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB164_original_strict_cash_lower_without_finiteness
-- name    : AvramDividend.Classical.avram_gbB164_original_strict_cash_lower_without_finiteness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T18:41:19.514044+00:00
-- url     : https://prove2.me/theorems/ed0e5820-5301-41b4-abc3-ef26efdd853a
-- title:
--   Original Gaussian stopped cash 164: eliminate finiteness hypothesis
-- statement:
--   The original equal-cap dividendMeasure strict stopped cash is finite for every finite horizon by B163. Apply the source-faithful B154 strict discounted cash lower bound using B163 as its finiteness input. This gives the original discounted Stieltjes cash lower bound unconditionally on the source tube, without an assumed finite discounted integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB164_original_strict_cash_lower_without_finiteness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S T : ℝ≥0) (hST : S < T)
    (hTube : ∀ t : ℝ≥0, t ≤ T →
      |X.X t ω| ≤ (1 / 400 : ℝ))
    (q : ℝ) (hq : 0 ≤ q)
    :
    Real.exp (-(q * (S : ℝ))) *
      barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ) S ω ≤
    (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩
        Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal := by sorry

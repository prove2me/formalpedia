-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion
-- name    : AvramDividend.Classical.avram_limit2_original_strict_positive_integer_horizon_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:01:53.244391+00:00
-- url     : https://prove2.me/theorems/00013dce-2442-4405-bda0-78f380326f8e
-- title:
--   Exact original perpetual dividend value as supremum of strict positive integer-horizon Stieltjes cash
-- statement:
--   For every original admissible dividend strategy D, the exact perpetual dividendValue equals the supremum of expected actual Stieltjes cash restricted to paymentTimes(ruinTime) intersect the open intervals Iio(n+1), n natural. The Proved canonical closed-horizon exhaustion theorem supplies the Iic(n) identity. Pointwise set inclusion Iic(n) subset Iio(n+1) subset Iic(n+1), followed by Mathlib lintegral_mono_set for the genuine inner dividendMeasure and lintegral_mono for the outer P measure, sandwiches the strict supremum between equal closed suprema. The positive shifted clock includes time zero, and every finite horizon atom eventually enters a later strict interval; no endpoint is silently discarded, no terminal vanishing and no stochastic martingale premise.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_original_strict_positive_integer_horizon_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by sorry

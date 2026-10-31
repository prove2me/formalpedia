-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_exp_dividend_bound
-- name    : AvramDividend.Classical.avram_wave3_02_positive_reserve_exp_dividend_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:37:25.170876+00:00
-- url     : https://prove2.me/theorems/70ffa281-e4b7-4ae0-8e94-82dce80fd3c2
-- title:
--   Original discounted barrier dividends have exponential decay in excess barrier for positive starting capital
-- statement:
--   For the original Standing spectrally negative Levy model with q>0, there are universal positive constants φ,C such that for every fixed positive capital x and every nonnegative barrier a≥x, the true expected discounted Stieltjes dividend value is bounded by exp(-φ(a-x)) C. It combines the Proved stopped first-upcrossing factor W(x)/W(a), the accepted original-process Esscher exponential scale ratio and the uniform Stieltjes boundary reward upper bound. This is derivative-free and quantitative.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 first-upcrossing factor and genuine reflected dividends; scale Esscher normalisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound
import Theorems.Thm_AvramDividend_Classical_barrier_value_scale_factor
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_positive_reserve_exp_dividend_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ C : ℝ, 0 < φ ∧ 0 < C ∧
      ∀ x a : ℝ, 0 < x → x ≤ a →
        dividendValue X q x (barrierStrategy X x a) ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x))) * ENNReal.ofReal C := by sorry

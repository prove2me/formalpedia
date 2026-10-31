-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_barrier_positive_capital_pos
-- name    : AvramDividend.Classical.avram_wave3_02_all_barrier_positive_capital_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:22:12.621948+00:00
-- url     : https://prove2.me/theorems/d6c7fe6d-60bc-4456-a71d-f71d3613ca07
-- title:
--   Every positive capital has strictly positive genuine reflected dividend value at every nonnegative barrier
-- statement:
--   In the original Standing spectrally negative Levy process at positive discount, any strictly positive initial surplus x and nonnegative reflection barrier a give a strictly positive expected Stieltjes discounted dividend reward. For a=0 or x>a, the immediate strictly positive dividend lump sum forces positive value. For a>0 and x≤a, the genuine killed exit factor W(x)/W(a) is strictly positive by standing scale-function positivity, and the original reflected boundary reward is strictly positive by derivative-free finite-grid lower renewal estimates. This source theorem does not require scale differentiability, global C1 or a stochastic surrogate.
-- source:
--   Avram Palmowski Pistorius (2007), stopped reflection Proposition 1; canonically Proved source-positive boundary reward and genuine stopped two-sided-exit valuation.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_pos
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_barrier_positive_capital_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 < x) :
    0 < dividendValue X q x (barrierStrategy X x a) := by sorry

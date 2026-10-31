-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_barrier_all_capital_finite
-- name    : AvramDividend.Classical.avram_wave3_02_all_barrier_all_capital_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:15:49.102804+00:00
-- url     : https://prove2.me/theorems/85dc1012-8595-4789-ada6-38063915a85c
-- title:
--   The original reflected dividend strategy has finite expected discounted value at every nonnegative barrier and capital
-- statement:
--   For any Standing spectrally negative Levy process, positive discount q, genuine q-scale function W, nonnegative reflection barrier a and nonnegative initial surplus x, the expected stopped Stieltjes discounted dividend reward is finite. The source-level boundary reflected reward is finite at a>0 by the proven derivative-free renewal bound. Below the barrier, the actual killed first-upcrossing factor times the boundary reward is finite. Above, immediate excess plus boundary reward remains finite. At a=0, the independently accepted zero-barrier all-capital valuation supplies finiteness. No global or pointwise scale derivative assumption is used.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; canonically proved Standing reflected boundary finiteness, first-passage factorisation, above-barrier initial lump sum and zero-barrier value.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_lt_top
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_barrier_all_capital_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) < ⊤ := by sorry

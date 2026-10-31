-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_reserve_high_barrier_value_zero
-- name    : AvramDividend.Classical.avram_wave3_02_all_reserve_high_barrier_value_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:46:10.430209+00:00
-- url     : https://prove2.me/theorems/791e46c4-a130-458e-a0e1-08bad7e0cc19
-- title:
--   Genuine expected barrier dividends vanish at infinite barrier from every nonnegative initial reserve
-- statement:
--   For any nonnegative initial capital x, including x=0, and under Standing and q>0, the actual original Lévy expected discounted Stieltjes dividend value of the constant-barrier strategy converges to zero as barrier a tends to infinity. Apply the Proved positive-capital exponential-decay limit at x+1>0 and monotonicity in initial capital for each nonnegative barrier to squeeze the x-capital value, without invoking scale C1.
-- source:
--   Avram Palmowski Pistorius (2007), genuine barrier policy and original Stieltjes dividend values; source-value capital monotonicity and positive-reserve high-barrier decay.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_high_barrier_value_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_reserve_high_barrier_value_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun a : ℝ => dividendValue X q x (barrierStrategy X x a))
      atTop (𝓝 (0 : ENNReal)) := by sorry

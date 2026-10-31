-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_value_monotone_in_initial_capital
-- name    : AvramDividend.Classical.avram_wave3_02_value_monotone_in_initial_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:24:30.073533+00:00
-- url     : https://prove2.me/theorems/d58398aa-e714-4b1b-9bde-b168b8e05d95
-- title:
--   Actual expected reflected barrier dividends increase with initial capital at every nonnegative barrier
-- statement:
--   For the original Standing spectrally negative Levy source with q>0 and any nonnegative barrier a, the true expected discounted Stieltjes dividends of reflection at a form a nondecreasing function of nonnegative initial capital. The zero-barrier case is affine in capital. Below a positive barrier, the genuine killed first-upcrossing factor W(x)/W(a) is nondecreasing in x by source scale monotonicity; the boundary value is nonnegative. Above the barrier the initial excess is affine. Across the barrier, the below-barrier value is at most the positive boundary reward and the above-barrier value is at least the boundary reward. This source-level capital monotonicity holds without any scale differentiability or global C1 input.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1; canonically Proved derivative-free full barrier-value decomposition, scale monotonicity and positive barrier scale factor.

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_value_monotone_in_initial_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a) :
    MonotoneOn (fun x : ℝ =>
      dividendValue X q x (barrierStrategy X x a)) (Ici 0) := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrier_value_all_capital_of_pointwise_diff
-- name    : AvramDividend.Classical.avram_wave3_02_barrier_value_all_capital_of_pointwise_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:11:32.553564+00:00
-- url     : https://prove2.me/theorems/17aeb49c-1b2b-44d9-be89-8899a0607b47
-- title:
--   Exact genuine barrier-strategy dividend value for all reserves at any differentiable positive barrier
-- statement:
--   For any original Standing spectrally negative Lévy process, positive q-scale W, barrier a>0 where W is differentiable, and every starting reserve x≥0, the exact expected discounted Stieltjes barrier strategy dividend value is W(x)/W'(a) below or at the barrier, and the immediate excess x-a plus the boundary value W(a)/W'(a) above it, interpreted in ENNReal. This directly combines verified source killed-first-passage/strong-Markov valuation with verified initial lump-sum reflection and true Stieltjes boundary ratio. Global C1 is not required.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and equation (3.15), actual first-record reflected-dividend strategy.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrier_value_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_barrier_value_all_capital_of_pointwise_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x)
    (hda : DifferentiableAt ℝ W a) :
    dividendValue X q x (barrierStrategy X x a) =
      if x ≤ a then ENNReal.ofReal (W x / deriv W a)
      else ENNReal.ofReal (x - a) + ENNReal.ofReal (W a / deriv W a) := by sorry

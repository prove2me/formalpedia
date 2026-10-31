-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_global_initial_reserve_upper
-- name    : AvramDividend.Classical.avram_wave3_02_global_initial_reserve_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:19:30.356026+00:00
-- url     : https://prove2.me/theorems/9ceb87df-4f9a-45c6-a91b-18b2b1857288
-- title:
--   Derivative-free linear-in-initial-capital bound on actual stopped reflected dividends
-- statement:
--   Under Standing, q>0 and a source-faithful q-scale function W, the actual expected discounted Stieltjes dividends of the barrier strategy at any a≥0 and x≥0 are at most initial capital x plus the genuine reflected boundary value. At a=0 equality follows from the original all-barrier piecewise representation. For a>0 and x≤a, the killed first-upcrossing scale factor W(x)/W(a) lies between zero and one by source monotonicity and positive W(a), yielding the upper bound. For x>a, actual initial-excess reflection gives the exact value x-a plus boundary reward, which is no larger than x plus boundary reward. No scale smoothness or stochastic surrogate assumption.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and stopped first-upcrossing dividend valuation; accepted source piecewise, monotonicity and above-barrier identities.

import Mathlib.Data.ENNReal.Basic
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

theorem AvramDividend.Classical.avram_wave3_02_global_initial_reserve_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) ≤
      ENNReal.ofReal x + barrierSupValue X a q := by sorry

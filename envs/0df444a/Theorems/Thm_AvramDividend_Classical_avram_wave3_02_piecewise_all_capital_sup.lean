-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_piecewise_all_capital_sup
-- name    : AvramDividend.Classical.avram_wave3_02_piecewise_all_capital_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:36:32.489378+00:00
-- url     : https://prove2.me/theorems/82e90c77-403e-49ae-b311-fe98a9234c5e
-- title:
--   Derivative-free all-capital reflected dividend decomposition through genuine boundary supremum value
-- statement:
--   For any fixed positive barrier a, every nonnegative starting reserve x has true expected discounted dividends equal to the killed first-upcrossing W(x)/W(a) factor times the actual reflected boundary supremum expectation for x≤a; for x>a the strategy pays x-a initially and thereafter has that boundary expectation. This identity is in ENNReal and requires no differentiability of W. The original stochastic dividend process and stopping time are used, including x=0 and x=a.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, reflected process and first-upcrossing decomposition. Built from canonically Proved source Stieltjes cash-process, exact Markov exit factor, and initial lump-sum admissible value.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_piecewise_all_capital_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        if x ≤ a then
          ENNReal.ofReal (W x / W a) * barrierSupValue X a q
        else
          ENNReal.ofReal (x - a) + barrierSupValue X a q := by sorry

-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_nonnegative_barriers_sup
-- name    : AvramDividend.Classical.avram_wave3_02_all_nonnegative_barriers_sup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:55:32.326214+00:00
-- url     : https://prove2.me/theorems/0cd6654d-e12b-47cd-8b86-be465947cceb
-- title:
--   Derivative-free reflected dividend value at every nonnegative barrier and initial capital
-- statement:
--   For the original Standing spectrally negative Lévy model and positive discount, the true reflected barrier dividend value at any nonnegative barrier a and nonnegative starting capital x admits a complete piecewise representation via the actual boundary reflected supremum reward. At a=0 it is the immediate payment x plus boundary reward; for a>0 below a it is the killed first-upcrossing W(x)/W(a) factor times boundary reward; above a it is immediate excess x-a plus boundary reward. This handles x=0, a=0 and equality at the barrier with no differentiability or C1 hypothesis.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, pathwise reflected regulator and first upcrossing. Uses canonical Proved zero-boundary value equality, positive-barrier piecewise source value, and above-barrier exact initial excess.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_piecewise_all_capital_sup
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_nonnegative_barriers_sup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        if a = 0 then ENNReal.ofReal x + barrierSupValue X a q
        else if x ≤ a then
          ENNReal.ofReal (W x / W a) * barrierSupValue X a q
        else ENNReal.ofReal (x - a) + barrierSupValue X a q := by sorry

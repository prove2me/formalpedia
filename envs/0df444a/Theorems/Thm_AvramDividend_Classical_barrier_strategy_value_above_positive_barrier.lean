-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_above_positive_barrier
-- name    : AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:14:11.345738+00:00
-- url     : https://prove2.me/theorems/05927a3a-a296-46b5-8e6b-2c482a11f5a4
-- title:
--   Barrier value formula above a positive barrier, including the initial excess payment
-- statement:
--   For a positive barrier a and initial surplus x>a, the barrier strategy pays x-a at time zero and then follows the barrier strategy from a. Its value is therefore x-a plus W(a)/W'(a), exactly the above-barrier branch of barrierValue. This isolates the initial-excess case omitted by the existing barrier_strategy_value milestone, which assumes x<=a.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, equations (3.12)-(3.14), pp.7-9, together with the immediate initial excess payment convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_strategy_value_above_positive_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by sorry

end AvramDividend.Classical

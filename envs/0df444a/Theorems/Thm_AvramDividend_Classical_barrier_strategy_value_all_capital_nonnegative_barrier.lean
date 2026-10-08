-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_all_capital_nonnegative_barrier
-- name    : AvramDividend.Classical.barrier_strategy_value_all_capital_nonnegative_barrier
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:11:33.079987+00:00
-- url     : https://prove2.me/theorems/a29f337e-f183-4d4a-a914-b85ec9e592dc
-- title:
--   Proposition 1 for all nonnegative barriers and initial surpluses
-- statement:
--   For any nonnegative barrier a and initial surplus x>=0, the discounted value of the constant barrier strategy equals the barrier-value formula v_a(x). This is Proposition 1 with the formal endpoint convention at a=0 and with the x>a initial excess payment included. For 0<a and x<=a it reduces to W(x)/W'(a); for x>a it is x-a plus the value at a; at a=0 scaleDeriv uses W'(0+).
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, Proposition 1, equations (3.12)-(3.14), pp.7-9, including the a=0 convention described later in the paper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_strategy_value_all_capital_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by sorry

end AvramDividend.Classical

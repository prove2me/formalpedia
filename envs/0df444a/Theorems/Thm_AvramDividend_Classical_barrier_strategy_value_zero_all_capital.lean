-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
-- name    : AvramDividend.Classical.barrier_strategy_value_zero_all_capital
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:13:54.709022+00:00
-- url     : https://prove2.me/theorems/d73a6aec-f808-4bc8-935d-5004c5b67597
-- title:
--   Barrier value formula at the zero barrier for every nonnegative initial surplus
-- statement:
--   At barrier a=0, reflection pays all positive surplus immediately and thereafter reflects at zero. For every x>=0 its discounted dividend value is the paper's zero-barrier formula v_0(x)=x+W(0)/W'(0+), with the scaleDeriv/divE convention for an infinite right derivative. This is the endpoint case of Proposition 1 needed when c*=0.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the zero-barrier convention described around pp.8 and 13-15.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrier_strategy_value_zero_all_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by sorry

end AvramDividend.Classical

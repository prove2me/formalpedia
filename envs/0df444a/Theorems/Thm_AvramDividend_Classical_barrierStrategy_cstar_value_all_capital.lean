-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_value_all_capital
-- name    : AvramDividend.Classical.barrierStrategy_cstar_value_all_capital
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:10:07.236274+00:00
-- url     : https://prove2.me/theorems/02cd610e-7b93-40c4-abbd-5b2bc43c94f5
-- title:
--   Proposition 1 at finite c*: the barrier policy value equals vcstar for every nonnegative initial surplus
-- statement:
--   Assume c* is finite. For every x>=0, the expected discounted dividends of reflection at c* equal the candidate barrier value vcstar(W,x). For 0<=x<=c* this is Proposition 1, W(x)/W'(c*). For x>c* it includes the initial lump sum x-c* plus the continuation value at c*. The endpoint c*=0 uses the paper's W'(0+) convention encoded by scaleDeriv/divE.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Proposition 1 (pp.7-9), definition (5.1), and Theorem 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_cstar_value_all_capital {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry

end AvramDividend.Classical

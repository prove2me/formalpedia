-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
-- name    : AvramDividend.Classical.barrierStrategy_value_eq_exit_factor
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T18:29:03.640462+00:00
-- url     : https://prove2.me/theorems/870df5c1-832c-45e2-ab50-320b83ed39af
-- title:
--   Barrier value below the barrier factors through the two-sided exit probability
-- statement:
--   Starting below a positive barrier, no dividends are paid before the process first reaches the barrier. By the strong Markov property, the barrier value is therefore the discounted probability of reaching a before ruin, W^(q)(x)/W^(q)(a), times the boundary reflected-supremum value.
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, Proposition 1, pp. 7–8. Its proof applies the strong Markov property at the first hit of the reflected process at zero and inserts the two-sided exit identity (3.6), giving the factor W^(q)(x)/W^(q)(a).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierStrategy_value_eq_exit_factor {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / W a) * barrierSupValue X a q := by sorry

end AvramDividend.Classical

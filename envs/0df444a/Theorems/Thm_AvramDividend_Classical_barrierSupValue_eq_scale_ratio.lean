-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
-- name    : AvramDividend.Classical.barrierSupValue_eq_scale_ratio
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T18:24:28.87968+00:00
-- url     : https://prove2.me/theorems/a8d4c941-496f-496a-987a-2a9b89bbf470
-- title:
--   Discounted reflected-supremum value at a barrier
-- statement:
--   For a positive barrier a, the expected discounted Stieltjes integral of the running supremum until the reflected process crosses the drawdown barrier equals W^(q)(a)/W^(q)'(a). This is the boundary case of the barrier dividend value formula.
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, Proposition 1 and equation (3.13), pp. 7–8: E_0[∫_0^{τ̂_a} e^{-qt} dS_t] = W^(q)(a)/W^(q)'(a).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem barrierSupValue_eq_scale_ratio {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by sorry

end AvramDividend.Classical

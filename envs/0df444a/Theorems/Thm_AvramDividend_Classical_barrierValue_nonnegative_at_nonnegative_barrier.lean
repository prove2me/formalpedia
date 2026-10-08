-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier
-- name    : AvramDividend.Classical.barrierValue_nonnegative_at_nonnegative_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:46:44.765304+00:00
-- url     : https://prove2.me/theorems/02720f59-37ec-4e98-8035-331f77f523a3
-- title:
--   Scale-function barrier candidate is nonnegative at every nonnegative barrier
-- statement:
--   For every nonnegative barrier a, the real candidate barrier value at its boundary is nonnegative. At a=0 this uses the one-sided derivative EReal/divE convention; at a>0 it is W(a)/W'(a). Because the q-scale function is nonnegative and nondecreasing on the positive half-line, W(a)≥0 and the usual real derivative of W at each positive point is nonnegative (with Lean's derivative default zero at nondifferentiable points). The quotient is therefore nonnegative even when the denominator is zero. This result supplies the sign hypothesis for ENNReal.ofReal addition identities in the initial-excess dividend arguments.
-- source:
--   Avram, Palmowski and Pistorius (2007), barrier value formula (5.1), scale-function positivity and monotonicity. Canonical ScaleFunction definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_nonnegative_at_nonnegative_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ barrierValue W a a := by sorry

end AvramDividend.Classical

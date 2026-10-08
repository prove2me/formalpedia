-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital
-- name    : AvramDividend.Classical.barrierValue_nonnegative_for_nonnegative_capital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:58:51.517475+00:00
-- url     : https://prove2.me/theorems/861b7656-5bc3-4d92-81da-da184060de56
-- title:
--   The constant-barrier value candidate is nonnegative at every nonnegative initial surplus
-- statement:
--   The candidate real value of a constant barrier strategy is nonnegative for every barrier a≥0 and initial capital x≥0. Below a positive barrier it is W(x)/W'(a), whose numerator and denominator are nonnegative by scale-function monotonicity and the derivative-sign lemma. At a=0,x=0 it is the separately proved zero-boundary value. Above a it is the sum x−a+barrierValue W a a; both terms are nonnegative by the already Proved all-barrier boundary result. This supports translating between real barrier formulae and ENNReal.ofReal in the initial-excess decomposition.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the piecewise barrier value formula (5.1); verified Prove2Me boundary positivity results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem barrierValue_nonnegative_for_nonnegative_capital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ barrierValue W a x := by sorry
end AvramDividend.Classical

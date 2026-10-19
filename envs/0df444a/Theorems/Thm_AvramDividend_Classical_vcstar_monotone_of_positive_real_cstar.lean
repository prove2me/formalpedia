-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_positive_real_cstar
-- name    : AvramDividend.Classical.vcstar_monotone_of_positive_real_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T10:23:45.828557+00:00
-- url     : https://prove2.me/theorems/d9b236d2-77d2-4838-b312-ed0e035175dd
-- title:
--   Positive canonical dividend barrier value is globally monotone
-- statement:
--   For an exact q-scale function W under the pinned IsScaleFunction axioms and a strictly positive real canonical cstar, the actual barrier value vcstar W is globally nondecreasing on ℝ. The positive barrier uses the ordinary derivative denominator deriv W a (not the problematic zero-barrier liminf), which is nonnegative because W is globally monotone. The real totalised division by a nonnegative denominator preserves nonnegativity and order, including the zero-denominator case. The piecewise zero/scaled/affine value then glues to a monotone function. This discharges the monotonicity premise of the far-field negative-jump HJB lemma.

import Mathlib.Algebra.Order.GroupWithZero.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_monotone_of_positive_real_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal) :
    Monotone (vcstar W) := by sorry

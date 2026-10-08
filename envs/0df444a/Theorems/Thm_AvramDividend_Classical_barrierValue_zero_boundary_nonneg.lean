-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_zero_boundary_nonneg
-- name    : AvramDividend.Classical.barrierValue_zero_boundary_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:31:01.723655+00:00
-- url     : https://prove2.me/theorems/3969db7b-e0d3-41cb-a64d-5b3a25e6d85b
-- title:
--   The zero-barrier scale-function candidate has nonnegative value
-- statement:
--   The zero-barrier candidate is nonnegative under the standing assumptions. The q-scale function is nonnegative and nondecreasing, so its right-derivative lower-limit at zero is nonnegative in EReal. The divE convention sends an infinite derivative to zero, and any finite nonnegative derivative gives a nonnegative quotient under the zero-denominator convention. This is the purely real-analytic component of the zero-barrier boundary formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and zero-barrier derivative convention; formal IsScaleFunction and divE definitions in ScaleFunction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem barrierValue_zero_boundary_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    0 ≤ barrierValue W 0 0 := by sorry

end AvramDividend.Classical

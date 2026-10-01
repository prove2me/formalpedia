-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
-- name    : AvramDividend.Classical.scaleDeriv_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T14:40:26.481469+00:00
-- url     : https://prove2.me/theorems/3f19a0fb-a939-4bf4-8dd7-0f4b6a047b68
-- title:
--   The q-scale-function derivative is nonnegative on the positive half-line
-- statement:
--   A q-scale function is nondecreasing on the nonnegative half-line by definition, hence wherever the ordinary derivative is taken at a positive point its derivative is nonnegative. In Lean, deriv is zero at non-differentiability points, so this follows directly from monotonicity without additional smoothness assumptions.
-- source:
--   Elementary real-analysis consequence of the monotonicity clause in IsScaleFunction; compatible with Avram, Palmowski, Pistorius, arXiv:math/0702893v1, Section 3.1 and Lemma 2(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleDeriv_nonneg {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 < x → 0 ≤ deriv W x := by sorry

end AvramDividend.Classical

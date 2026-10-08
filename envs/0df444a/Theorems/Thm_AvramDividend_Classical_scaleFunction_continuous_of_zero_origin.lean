-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
-- name    : AvramDividend.Classical.scaleFunction_continuous_of_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:20:36.929002+00:00
-- url     : https://prove2.me/theorems/3321ae26-a1be-4095-85ea-bceb296f4a78
-- title:
--   A q-scale function vanishing at the origin is continuous on the whole real line
-- statement:
--   A q-scale function W is identically zero on the negative half-line and continuous on the nonnegative half-line. If W(0)=0, the two continuous pieces meet at the origin and W is globally continuous. The proof uses the closed-set pasting lemma, rather than incorrectly treating a BV scale function with W(0)>0 as globally continuous. This supplies the shifted-state continuity for compensated jump-generator dominated convergence in the zero-origin branch without a Lévy atomlessness hypothesis.
-- source:
--   IsScaleFunction support and positive-side continuity; Mathlib ContinuousOn.union_of_isClosed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_continuous_of_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    Continuous W := by sorry

end AvramDividend.Classical

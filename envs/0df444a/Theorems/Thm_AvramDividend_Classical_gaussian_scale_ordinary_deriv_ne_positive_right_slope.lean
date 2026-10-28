-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_scale_ordinary_deriv_ne_positive_right_slope
-- name    : AvramDividend.Classical.gaussian_scale_ordinary_deriv_ne_positive_right_slope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:08:50.853007+00:00
-- url     : https://prove2.me/theorems/1a30e35a-7d5b-4272-903f-8b6074956756
-- title:
--   Gaussian scale ordinary derivative at zero cannot equal the positive one-sided slope
-- statement:
--   For every positive Gaussian q-scale, W(0)=0 by an already Proved theorem. Its canonical support on the nonnegative axis makes zero a local minimum, so the ordinary two-sided real derivative at zero is zero by another Proved theorem. Since sigma>0, 2/sigma squared is strictly positive; the ordinary derivative therefore cannot equal the Gaussian right-hand slope. This precisely refutes the ordinary-deriv W 0 normalisation mistakenly used in some older generator lemmas, while leaving the separately proved right-limit statement intact.
-- source:
--   Proved scaleFunction_zero_origin_gaussian_without_standing and scaleFunction_ordinary_deriv_zero_at_origin, elementary real arithmetic.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_ordinary_deriv_zero_at_origin
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- Gaussian q-scale's ordinary derivative at the origin differs from its positive right slope. -/
theorem gaussian_scale_ordinary_deriv_ne_positive_right_slope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    deriv W 0 ≠ 2 / X.σ ^ 2 := by
  sorry
end AvramDividend.Classical

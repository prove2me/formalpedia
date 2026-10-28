-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scaleFunction_nonpositive_discount_eq_zero
-- name    : AvramDividend.Classical.unbounded_scaleFunction_nonpositive_discount_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:22:30.87951+00:00
-- url     : https://prove2.me/theorems/913a439b-6339-45d6-bd0a-71508deb4d87
-- title:
--   Nonpositive discount equals zero for an unbounded-variation scale function
-- statement:
--   The mission's root-connected nonpositive-discount C1 leaf can only have q=0. For q<0, a Proved theorem derives a contradiction from scale-function integrability and positivity. Thus any q≤0 admitting a scale function under unbounded variation must equal zero. This cleanly isolates zero-discount C1 as the remaining substantive analytic case.
-- source:
--   Proved unbounded_scaleFunction_negative_q_impossible

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_scaleFunction_negative_q_impossible
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scaleFunction_nonpositive_discount_eq_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : q ≤ 0)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) : q = 0 := by sorry

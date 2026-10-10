-- Prove2me | Theorems.Thm_BookProof_LocalityConstraint_restrict_graphSet_eq_zero
-- name    : BookProof.LocalityConstraint.restrict_graphSet_eq_zero
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:32:13.017555+00:00
-- url     : https://prove2.me/theorems/9821c86a-f5bd-4ca4-a6a1-36e5951616bc
-- title:
--   `BookProof.LocalityConstraint.restrict_graphSet_eq_zero` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : (μ.prod ν).restrict (g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalityConstraintNull`.
--
--   `BookProof.LocalityConstraint.restrict_graphSet_eq_zero` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : (μ.prod ν).restrict (graphSet f) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.LocalityConstraint.restrict_graphSet_eq_zero`.

-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.restrict_graphSet_eq_zero
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem BookProof.LocalityConstraint.restrict_graphSet_eq_zero (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν).restrict (graphSet f) = 0 := by sorry

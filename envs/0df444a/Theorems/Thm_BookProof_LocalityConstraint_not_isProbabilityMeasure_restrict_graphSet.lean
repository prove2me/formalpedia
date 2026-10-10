-- Prove2me | Theorems.Thm_BookProof_LocalityConstraint_not_isProbabilityMeasure_restrict_graphSet
-- name    : BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:33:12.083814+00:00
-- url     : https://prove2.me/theorems/01329791-b2bd-4138-a044-6d579dec409c
-- title:
--   `BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : ¬ IsP
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalityConstraintNull`.
--
--   `BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : ¬ IsProbabilityMeasure ((μ.prod ν).restrict (graphSet f))
--
--   Formalization note: Lean 4 identifier `BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet`.

-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet (μ : Measure α) (ν : Measure ℝ)
    [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) :
    ¬ IsProbabilityMeasure ((μ.prod ν).restrict (graphSet f)) := by sorry

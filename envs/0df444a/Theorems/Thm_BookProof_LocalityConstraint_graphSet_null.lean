-- Prove2me | Theorems.Thm_BookProof_LocalityConstraint_graphSet_null
-- name    : BookProof.LocalityConstraint.graphSet_null
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:56.047429+00:00
-- url     : https://prove2.me/theorems/93bd199e-ced8-4f5b-9d34-2c84b6ad1b7c
-- title:
--   `BookProof.LocalityConstraint.graphSet_null` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : (μ.prod ν) (graphSet f) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalityConstraintNull`.
--
--   `BookProof.LocalityConstraint.graphSet_null` (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν] {f : α → ℝ} (hf : Measurable f) : (μ.prod ν) (graphSet f) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.LocalityConstraint.graphSet_null`.

-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.graphSet_null
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem BookProof.LocalityConstraint.graphSet_null (μ : Measure α) (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    {f : α → ℝ} (hf : Measurable f) :
    (μ.prod ν) (graphSet f) = 0 := by sorry

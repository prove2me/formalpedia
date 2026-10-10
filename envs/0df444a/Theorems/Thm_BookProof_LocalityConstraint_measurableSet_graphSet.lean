-- Prove2me | Theorems.Thm_BookProof_LocalityConstraint_measurableSet_graphSet
-- name    : BookProof.LocalityConstraint.measurableSet_graphSet
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:57.175623+00:00
-- url     : https://prove2.me/theorems/050b0a40-0229-4f4c-afa9-08e29c6bac74
-- title:
--   `BookProof.LocalityConstraint.measurableSet_graphSet` {f : α → ℝ} (hf : Measurable f) : MeasurableSet (graphSet f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalityConstraintNull`.
--
--   `BookProof.LocalityConstraint.measurableSet_graphSet` {f : α → ℝ} (hf : Measurable f) : MeasurableSet (graphSet f)
--
--   Formalization note: Lean 4 identifier `BookProof.LocalityConstraint.measurableSet_graphSet`.

-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.measurableSet_graphSet
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem BookProof.LocalityConstraint.measurableSet_graphSet {f : α → ℝ} (hf : Measurable f) :
    MeasurableSet (graphSet f) := by sorry

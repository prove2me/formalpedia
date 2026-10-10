-- Prove2me | Theorems.Thm_BookProof_LocalityConstraint_graphSet_gaussian_null
-- name    : BookProof.LocalityConstraint.graphSet_gaussian_null
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T12:32:45.43153+00:00
-- url     : https://prove2.me/theorems/0d4990b5-eb62-4eb5-9ecb-51f6fc3b3ce1
-- title:
--   `BookProof.LocalityConstraint.graphSet_gaussian_null` (m₁ m₂ : ℝ) (v₁ : ℝ≥0) (v₂ : ℝ≥0) (hv₂ : v₂ ≠ 0) {f : ℝ → ℝ} (hf : Measurable f) : ((gaussianReal m₁...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLocalityConstraintNull`.
--
--   `BookProof.LocalityConstraint.graphSet_gaussian_null` (m₁ m₂ : ℝ) (v₁ : ℝ≥0) (v₂ : ℝ≥0) (hv₂ : v₂ ≠ 0) {f : ℝ → ℝ} (hf : Measurable f) : ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)) (graphSet f) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.LocalityConstraint.graphSet_gaussian_null`.

-- Generated from ChapterLocalityConstraintNull.lean — theorem BookProof.LocalityConstraint.graphSet_gaussian_null
import Mathlib
import Definitions.Def_ChapterLocalityConstraintNull
open BookProof.LocalityConstraint



open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

theorem BookProof.LocalityConstraint.graphSet_gaussian_null (m₁ m₂ : ℝ) (v₁ : ℝ≥0) (v₂ : ℝ≥0) (hv₂ : v₂ ≠ 0)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ((gaussianReal m₁ v₁).prod (gaussianReal m₂ v₂)) (graphSet f) = 0 := by sorry

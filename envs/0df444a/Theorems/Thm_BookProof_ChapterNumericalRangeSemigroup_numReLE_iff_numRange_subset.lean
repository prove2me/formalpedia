-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeSemigroup_numReLE_iff_numRange_subset
-- name    : BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:14.419299+00:00
-- url     : https://prove2.me/theorems/cdef6a95-b712-41f5-9ae5-2cf9efbe1ea8
-- title:
--   `BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset` (A : E →L[ℂ] E) {ω : ℝ} : NumReLE A ω ↔ BookProof.ChapterH9.numRange A ⊆ {z : ℂ | z.re ≤ ω}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeSemigroup`.
--
--   `BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset` (A : E →L[ℂ] E) {ω : ℝ} : NumReLE A ω ↔ BookProof.ChapterH9.numRange A ⊆ {z : ℂ | z.re ≤ ω}
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset`.

-- Generated from ChapterNumericalRangeSemigroup.lean — theorem BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeSemigroup
import Definitions.Def_ChapterH9
open BookProof.ChapterH9
open BookProof.ChapterNumericalRangeSemigroup


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset (A : E →L[ℂ] E) {ω : ℝ} :
    NumReLE A ω ↔ BookProof.ChapterH9.numRange A ⊆ {z : ℂ | z.re ≤ ω} := by sorry

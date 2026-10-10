-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numRadiusLE_iff_numRange_subset
-- name    : BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:13:37.52487+00:00
-- url     : https://prove2.me/theorems/1a641b71-fd9a-4d94-b8d7-c4b82de5a58c
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset` [CompleteSpace E] (A : E →L[ℂ] E) {r : ℝ} : NumRadiusLE A r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.clos
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset` [CompleteSpace E] (A : E →L[ℂ] E) {r : ℝ} : NumRadiusLE A r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall (0 : ℂ) r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Definitions.Def_ChapterH9
open BookProof.ChapterH9
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.numRadiusLE_iff_numRange_subset [CompleteSpace E] (A : E →L[ℂ] E) {r : ℝ} :
    NumRadiusLE A r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall (0 : ℂ) r := by sorry

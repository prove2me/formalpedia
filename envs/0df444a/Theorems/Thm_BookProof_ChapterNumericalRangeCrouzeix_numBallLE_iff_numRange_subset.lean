-- Prove2me | Theorems.Thm_BookProof_ChapterNumericalRangeCrouzeix_numBallLE_iff_numRange_subset
-- name    : BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:16:04.800997+00:00
-- url     : https://prove2.me/theorems/0cf040e8-090d-4470-9b8b-e3c087dc4f45
-- title:
--   `BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset` [CompleteSpace E] (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} : NumBallLE A c r ↔ BookProof.ChapterH9.numRange A ⊆ Metri
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNumericalRangeCrouzeix`.
--
--   `BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset` [CompleteSpace E] (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} : NumBallLE A c r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall c r
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset`.

-- Generated from ChapterNumericalRangeCrouzeix.lean — theorem BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
import Definitions.Def_ChapterH9
open BookProof.ChapterH9
open BookProof.ChapterNumericalRangeCrouzeix


open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem BookProof.ChapterNumericalRangeCrouzeix.numBallLE_iff_numRange_subset [CompleteSpace E] (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} :
    NumBallLE A c r ↔ BookProof.ChapterH9.numRange A ⊆ Metric.closedBall c r := by sorry

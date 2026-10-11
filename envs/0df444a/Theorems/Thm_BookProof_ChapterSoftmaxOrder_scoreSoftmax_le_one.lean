-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_le_one
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:21.075018+00:00
-- url     : https://prove2.me/theorems/4e7f649d-a51b-4766-9c46-d566d538f0b8
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j ≤ 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta s j ≤ 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_le_one (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j ≤ 1 := by sorry

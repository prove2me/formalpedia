-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_shift
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:29.313615+00:00
-- url     : https://prove2.me/theorems/8adac1b9-6b78-4c27-a4bb-1d1ec27a9ead
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift` (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l + c) j = scoreSoftmax beta s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift` (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) : scoreSoftmax beta (fun l => s l + c) j = scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l + c) j = scoreSoftmax beta s j := by sorry

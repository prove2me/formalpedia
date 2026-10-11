-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_const
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:02.715601+00:00
-- url     : https://prove2.me/theorems/238d018a-bc99-4862-9167-b01cedbb65a2
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_const` (beta c : ℝ) (j : Fin m) : scoreSoftmax beta (fun _ => c) j = 1 / m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_const` (beta c : ℝ) (j : Fin m) : scoreSoftmax beta (fun _ => c) j = 1 / m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_const`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_const
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_const (beta c : ℝ) (j : Fin m) :
    scoreSoftmax beta (fun _ => c) j = 1 / m := by sorry

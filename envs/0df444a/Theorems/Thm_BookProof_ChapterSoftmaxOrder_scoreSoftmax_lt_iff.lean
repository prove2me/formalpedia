-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_lt_iff
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:46.762237+00:00
-- url     : https://prove2.me/theorems/f1ceb831-4816-4723-b3c6-cf8cc2b16c75
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta s i < scoreSoftmax beta s j ↔ s i < s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta s i < scoreSoftmax beta s j ↔ s i < s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_lt_iff {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta s i < scoreSoftmax beta s j ↔ s i < s j := by sorry

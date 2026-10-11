-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_nonneg
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:34:57.682976+00:00
-- url     : https://prove2.me/theorems/2c0702f2-3f97-45cf-b444-755949f8b08b
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : 0 ≤ scoreSoftmax beta s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : 0 ≤ scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_nonneg (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    0 ≤ scoreSoftmax beta s j := by sorry

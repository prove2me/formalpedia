-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_inj_iff
-- name    : BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:35:44.878238+00:00
-- url     : https://prove2.me/theorems/979a9f6b-1d5d-4f04-8472-4d6a285ceee8
-- title:
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta s i = scoreSoftmax beta s j ↔ s i = s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxOrder`.
--
--   `BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff` {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) : scoreSoftmax beta s i = scoreSoftmax beta s j ↔ s i = s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff`.

-- Generated from ChapterSoftmaxOrder.lean — theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff
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

theorem BookProof.ChapterSoftmaxOrder.scoreSoftmax_inj_iff {beta : ℝ} (hbeta : 0 < beta) (s : Fin m → ℝ) (i j : Fin m) :
    scoreSoftmax beta s i = scoreSoftmax beta s j ↔ s i = s j := by sorry

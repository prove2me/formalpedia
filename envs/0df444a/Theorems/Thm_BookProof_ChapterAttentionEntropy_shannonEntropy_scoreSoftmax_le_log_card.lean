-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_shannonEntropy_scoreSoftmax_le_log_card
-- name    : BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:55:50.572981+00:00
-- url     : https://prove2.me/theorems/dde55734-0321-49c1-8dda-06d704de8879
-- title:
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : shannonEntropy (fun j => scoreSoftmax beta s j) ≤ Real.log m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card` (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) : shannonEntropy (fun j => scoreSoftmax beta s j) ≤ Real.log m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_le_log_card (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    shannonEntropy (fun j => scoreSoftmax beta s j) ≤ Real.log m := by sorry

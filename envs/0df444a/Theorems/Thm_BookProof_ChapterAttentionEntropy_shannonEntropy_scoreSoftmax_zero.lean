-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_shannonEntropy_scoreSoftmax_zero
-- name    : BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:56:00.089976+00:00
-- url     : https://prove2.me/theorems/23ea274e-9169-45bb-8df2-c28d53c79376
-- title:
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero` (s : Fin m → ℝ) (hm : 0 < m) : shannonEntropy (fun j => scoreSoftmax 0 s j) = Real.log m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero` (s : Fin m → ℝ) (hm : 0 < m) : shannonEntropy (fun j => scoreSoftmax 0 s j) = Real.log m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero
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

theorem BookProof.ChapterAttentionEntropy.shannonEntropy_scoreSoftmax_zero (s : Fin m → ℝ) (hm : 0 < m) :
    shannonEntropy (fun j => scoreSoftmax 0 s j) = Real.log m := by sorry

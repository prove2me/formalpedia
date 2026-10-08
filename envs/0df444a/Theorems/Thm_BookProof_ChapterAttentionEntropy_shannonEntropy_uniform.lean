-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_shannonEntropy_uniform
-- name    : BookProof.ChapterAttentionEntropy.shannonEntropy_uniform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:55:39.388282+00:00
-- url     : https://prove2.me/theorems/197204d0-6387-4358-90ef-0f214d83e859
-- title:
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_uniform` (hm : 0 < m) : shannonEntropy (fun _ : Fin m => (1 : ℝ) / m) = Real.log m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.shannonEntropy_uniform` (hm : 0 < m) : shannonEntropy (fun _ : Fin m => (1 : ℝ) / m) = Real.log m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.shannonEntropy_uniform`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.shannonEntropy_uniform
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionEntropy
open BookProof.ChapterAttentionEntropy


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

theorem BookProof.ChapterAttentionEntropy.shannonEntropy_uniform (hm : 0 < m) :
    shannonEntropy (fun _ : Fin m => (1 : ℝ) / m) = Real.log m := by sorry

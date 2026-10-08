-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionEntropy_tendsto_shannonEntropy_scoreSoftmax
-- name    : BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:56:27.430282+00:00
-- url     : https://prove2.me/theorems/8fea198a-3b79-4157-8e66-0ca75d9bd377
-- title:
--   `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => shannonEntropy (fun l =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionEntropy`.
--
--   `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => shannonEntropy (fun l => scoreSoftmax b s l)) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax`.

-- Generated from ChapterAttentionEntropy.lean — theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax
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

theorem BookProof.ChapterAttentionEntropy.tendsto_shannonEntropy_scoreSoftmax (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => shannonEntropy (fun l => scoreSoftmax b s l)) atTop (𝓝 0) := by sorry

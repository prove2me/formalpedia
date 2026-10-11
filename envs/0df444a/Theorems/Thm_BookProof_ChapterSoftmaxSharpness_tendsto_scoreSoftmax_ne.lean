-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_ne
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:13.088867+00:00
-- url     : https://prove2.me/theorems/cbb9db89-41a5-4078-b3b2-c2e5d7398a45
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne` (s : Fin m → ℝ) (j i : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) (hi : i ≠ j) : Tendsto (fun b : ℝ => scoreSoftmax b s i) a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne` (s : Fin m → ℝ) (j i : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) (hi : i ≠ j) : Tendsto (fun b : ℝ => scoreSoftmax b s i) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_ne (s : Fin m → ℝ) (j i : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) (hi : i ≠ j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s i) atTop (𝓝 0) := by sorry

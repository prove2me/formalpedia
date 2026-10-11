-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_denom
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:36:57.989489+00:00
-- url     : https://prove2.me/theorems/b1029db3-c093-4e86-ba00-337e3aeabd91
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop (𝓝 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_denom (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => ∑ l, Real.exp (b * (s l - s j))) atTop (𝓝 1) := by sorry

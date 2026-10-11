-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_max
-- name    : BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:38:16.229136+00:00
-- url     : https://prove2.me/theorems/99fe4cf2-0d21-4627-bf46-7748c5ccd7d3
-- title:
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => scoreSoftmax b s j) atTop (𝓝 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, l ≠ j → s l < s j) : Tendsto (fun b : ℝ => scoreSoftmax b s j) atTop (𝓝 1)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.tendsto_scoreSoftmax_max (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, l ≠ j → s l < s j) :
    Tendsto (fun b : ℝ => scoreSoftmax b s j) atTop (𝓝 1) := by sorry

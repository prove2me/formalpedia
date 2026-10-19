-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_differentiable_scoreSoftmax
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:16:38.579971+00:00
-- url     : https://prove2.me/theorems/1268bd35-dabf-45eb-a668-858d3e79d3d4
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax` (s : Fin m → ℝ) (j : Fin m) : Differentiable ℝ fun b : ℝ => scoreSoftmax b s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax` (s : Fin m → ℝ) (j : Fin m) : Differentiable ℝ fun b : ℝ => scoreSoftmax b s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxTemperatureMonotone.differentiable_scoreSoftmax (s : Fin m → ℝ) (j : Fin m) :
    Differentiable ℝ fun b : ℝ => scoreSoftmax b s j := by sorry

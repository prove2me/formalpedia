-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_deriv_scoreSoftmax_beta
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T08:16:20.472332+00:00
-- url     : https://prove2.me/theorems/5daa38a3-7336-45b4-9b9e-1107a03c2aba
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : deriv (fun b : ℝ => scoreSoftmax b s j) beta = scoreSoftmax beta s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta` (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) : deriv (fun b : ℝ => scoreSoftmax b s j) beta = scoreSoftmax beta s j * (s j - meanScore beta s)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

theorem BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    deriv (fun b : ℝ => scoreSoftmax b s j) beta
      = scoreSoftmax beta s j * (s j - meanScore beta s) := by sorry

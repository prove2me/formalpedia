-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_max_ge_of_le
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:47.586832+00:00
-- url     : https://prove2.me/theorems/8a4d7acb-0ca9-446f-99b8-cd6daa3da2d4
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le` {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : scoreSoftmax bet
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le` {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : scoreSoftmax beta s j ≤ scoreSoftmax gamma s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ)
    (j : Fin m) (hmax : ∀ l, s l ≤ s j) :
    scoreSoftmax beta s j ≤ scoreSoftmax gamma s j := by sorry

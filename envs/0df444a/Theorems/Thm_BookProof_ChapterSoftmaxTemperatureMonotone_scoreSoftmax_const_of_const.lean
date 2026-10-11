-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_const_of_const
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:38:22.806613+00:00
-- url     : https://prove2.me/theorems/1d092dd1-d510-4ba3-bd57-bd858902911d
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const` {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c) (beta : ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / (m : ℝ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const` {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c) (beta : ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c)
    (beta : ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / (m : ℝ) := by sorry

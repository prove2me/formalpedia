-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_monotone_of_max
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:17:27.111126+00:00
-- url     : https://prove2.me/theorems/fc62406e-5fca-409f-bc5c-83700651a0b5
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : Monotone fun b : ℝ => scoreSoftmax b s j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max` (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : Monotone fun b : ℝ => scoreSoftmax b s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_monotone_of_max (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) :
    Monotone fun b : ℝ => scoreSoftmax b s j := by sorry

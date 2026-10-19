-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_antitone_of_min
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:16:16.543251+00:00
-- url     : https://prove2.me/theorems/70552e13-0e58-439c-8b5c-fbbe1b356a3d
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min` (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : Antitone fun b : ℝ => scoreSoftmax b s i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min` (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : Antitone fun b : ℝ => scoreSoftmax b s i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_antitone_of_min (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    Antitone fun b : ℝ => scoreSoftmax b s i := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_min_le_of_le
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:39:31.316838+00:00
-- url     : https://prove2.me/theorems/7093092e-9cbc-446e-a98e-97b991e8937f
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le` {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : scoreSoftmax gam
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le` {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : scoreSoftmax gamma s i ≤ scoreSoftmax beta s i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ)
    (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    scoreSoftmax gamma s i ≤ scoreSoftmax beta s i := by sorry

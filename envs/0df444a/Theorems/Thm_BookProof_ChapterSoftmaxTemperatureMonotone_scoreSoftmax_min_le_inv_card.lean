-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_min_le_inv_card
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:38:12.513788+00:00
-- url     : https://prove2.me/theorems/16849eb1-b4ca-4622-b5db-dc404e7b475a
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : scoreSoftmax beta s i ≤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m) (hmin : ∀ l, s i ≤ s l) : scoreSoftmax beta s i ≤ 1 / (m : ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_inv_card {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (i : Fin m)
    (hmin : ∀ l, s i ≤ s l) : scoreSoftmax beta s i ≤ 1 / (m : ℝ) := by sorry

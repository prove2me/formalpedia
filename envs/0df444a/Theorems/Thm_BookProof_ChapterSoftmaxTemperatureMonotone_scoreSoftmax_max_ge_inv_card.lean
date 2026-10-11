-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_max_ge_inv_card
-- name    : BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T14:38:06.476832+00:00
-- url     : https://prove2.me/theorems/31112880-9bde-46dd-a63c-23b5375b2430
-- title:
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : 1 / (m : ℝ) ≤ scoreSoftm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxTemperatureMonotone`.
--
--   `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card` {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m) (hmax : ∀ l, s l ≤ s j) : 1 / (m : ℝ) ≤ scoreSoftmax beta s j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card`.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card
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

theorem BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_inv_card {beta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ) (j : Fin m)
    (hmax : ∀ l, s l ≤ s j) : 1 / (m : ℝ) ≤ scoreSoftmax beta s j := by sorry

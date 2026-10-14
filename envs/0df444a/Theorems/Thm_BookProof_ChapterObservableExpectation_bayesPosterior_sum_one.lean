-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_bayesPosterior_sum_one
-- name    : BookProof.ChapterObservableExpectation.bayesPosterior_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:44:21.359228+00:00
-- url     : https://prove2.me/theorems/8d672c52-f2f7-4f5f-a0ee-1d2c640ed1f0
-- title:
--   `BookProof.ChapterObservableExpectation.bayesPosterior_sum_one` {prior : Fin m → ℝ} {L : Fin m → Y → ℝ} (y : Y) (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.bayesPosterior_sum_one` {prior : Fin m → ℝ} {L : Fin m → Y → ℝ} (y : Y) (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.bayesPosterior_sum_one`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.bayesPosterior_sum_one
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {Y : Type*}

theorem BookProof.ChapterObservableExpectation.bayesPosterior_sum_one {prior : Fin m → ℝ} {L : Fin m → Y → ℝ} (y : Y)
    (hy : 0 < evidence prior L y) : ∑ x, posterior prior L y x = 1 := by sorry

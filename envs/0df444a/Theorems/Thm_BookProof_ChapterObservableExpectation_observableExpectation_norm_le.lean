-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_norm_le
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_norm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:20.434961+00:00
-- url     : https://prove2.me/theorems/31152583-5aa2-46dc-a6bb-eb539cded69d
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_norm_le` {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_norm_le` {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) (v : Fin m → F) (C : ℝ) (hC : ∀ j, ‖v j‖ ≤ C) : ‖observableExpectation p v‖ ≤ C
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_norm_le`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_norm_le
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_norm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (p : Fin m → ℝ) (hp : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (v : Fin m → F) (C : ℝ) (hC : ∀ j, ‖v j‖ ≤ C) :
    ‖observableExpectation p v‖ ≤ C := by sorry

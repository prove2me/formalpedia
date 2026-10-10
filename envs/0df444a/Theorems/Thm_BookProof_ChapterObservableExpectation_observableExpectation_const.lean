-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_const
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:38:21.869744+00:00
-- url     : https://prove2.me/theorems/c8c4b8a7-6fc8-470f-b214-2605aed77499
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_const` (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (c : E) : observableExpectation p (fun _ => c) = c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_const` (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (c : E) : observableExpectation p (fun _ => c) = c
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_const`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_const
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_const (p : Fin m → ℝ) (hp : ∑ j, p j = 1) (c : E) :
    observableExpectation p (fun _ => c) = c := by sorry

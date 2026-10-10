-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_add_left
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_add_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:26.731429+00:00
-- url     : https://prove2.me/theorems/d03fa3b8-788a-4888-94cd-cca0352ef451
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_add_left` (p q : Fin m → ℝ) (v : Fin m → E) : observableExpectation (fun j => p j + q j) v = observableExpectation p v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_add_left` (p q : Fin m → ℝ) (v : Fin m → E) : observableExpectation (fun j => p j + q j) v = observableExpectation p v + observableExpectation q v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_add_left`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_add_left
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_add_left (p q : Fin m → ℝ) (v : Fin m → E) :
    observableExpectation (fun j => p j + q j) v
      = observableExpectation p v + observableExpectation q v := by sorry

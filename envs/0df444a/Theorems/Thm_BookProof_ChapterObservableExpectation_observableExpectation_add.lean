-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_add
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:38:40.474927+00:00
-- url     : https://prove2.me/theorems/4147cbdd-13a0-4ec3-af91-0feb2ac741f4
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_add` (p : Fin m → ℝ) (v w : Fin m → E) : observableExpectation p (fun j => v j + w j) = observableExpectation p v + ob
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_add` (p : Fin m → ℝ) (v w : Fin m → E) : observableExpectation p (fun j => v j + w j) = observableExpectation p v + observableExpectation p w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_add`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_add
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_add (p : Fin m → ℝ) (v w : Fin m → E) :
    observableExpectation p (fun j => v j + w j)
      = observableExpectation p v + observableExpectation p w := by sorry

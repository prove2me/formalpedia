-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_smul
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:19.290374+00:00
-- url     : https://prove2.me/theorems/11670eec-4401-4f88-a932-0bfa8ccc8c07
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_smul` (p : Fin m → ℝ) (c : ℝ) (v : Fin m → E) : observableExpectation p (fun j => c • v j) = c • observableExpectation
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_smul` (p : Fin m → ℝ) (c : ℝ) (v : Fin m → E) : observableExpectation p (fun j => c • v j) = c • observableExpectation p v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_smul`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_smul
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_smul (p : Fin m → ℝ) (c : ℝ) (v : Fin m → E) :
    observableExpectation p (fun j => c • v j) = c • observableExpectation p v := by sorry

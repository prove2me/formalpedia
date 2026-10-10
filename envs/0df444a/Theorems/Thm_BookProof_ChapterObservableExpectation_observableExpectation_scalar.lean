-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_observableExpectation_scalar
-- name    : BookProof.ChapterObservableExpectation.observableExpectation_scalar
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T08:38:33.912129+00:00
-- url     : https://prove2.me/theorems/91f1f627-f27e-4a84-a8cd-76f7da8d161e
-- title:
--   `BookProof.ChapterObservableExpectation.observableExpectation_scalar` (p v : Fin m → ℝ) : observableExpectation p v = ∑ j, p j * v j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.observableExpectation_scalar` (p v : Fin m → ℝ) : observableExpectation p v = ∑ j, p j * v j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.observableExpectation_scalar`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.observableExpectation_scalar
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.observableExpectation_scalar (p v : Fin m → ℝ) :
    observableExpectation p v = ∑ j, p j * v j := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_attention_eq_expectation
-- name    : BookProof.ChapterObservableExpectation.attention_eq_expectation
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:08.236025+00:00
-- url     : https://prove2.me/theorems/bce43855-3663-43b2-a239-b105df429e4f
-- title:
--   `BookProof.ChapterObservableExpectation.attention_eq_expectation` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) : (∀ j, 0 ≤ bor
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.attention_eq_expectation` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) : (∀ j, 0 ≤ bornWeight q k j) ∧ (∑ j, bornWeight q k j = 1) ∧ attentionOutput q k v = observableExpectation (bornWeight q k) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.attention_eq_expectation`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.attention_eq_expectation
import Mathlib
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterObservableExpectation


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn

variable {m n : ℕ}
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem BookProof.ChapterObservableExpectation.attention_eq_expectation (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) :
    (∀ j, 0 ≤ bornWeight q k j) ∧ (∑ j, bornWeight q k j = 1) ∧
      attentionOutput q k v = observableExpectation (bornWeight q k) v := by sorry

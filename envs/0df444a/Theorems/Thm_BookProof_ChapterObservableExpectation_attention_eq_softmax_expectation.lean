-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_attention_eq_softmax_expectation
-- name    : BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:21.466357+00:00
-- url     : https://prove2.me/theorems/0225d2b0-eb16-487b-88c7-7b98e4e37fb5
-- title:
--   `BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (v : F
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (v : Fin m → E) : attentionOutput q k v = observableExpectation (softmax 2 q k) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation
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

theorem BookProof.ChapterObservableExpectation.attention_eq_softmax_expectation (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r)
    (v : Fin m → E) :
    attentionOutput q k v = observableExpectation (softmax 2 q k) v := by sorry

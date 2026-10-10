-- Prove2me | Theorems.Thm_BookProof_ChapterObservableExpectation_attention_mem_convexHull
-- name    : BookProof.ChapterObservableExpectation.attention_mem_convexHull
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T08:39:19.522676+00:00
-- url     : https://prove2.me/theorems/992b732f-d063-49b2-9ed7-525a6fca0031
-- title:
--   `BookProof.ChapterObservableExpectation.attention_mem_convexHull` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) : attentionOutp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterObservableExpectation`.
--
--   `BookProof.ChapterObservableExpectation.attention_mem_convexHull` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) : attentionOutput q k v ∈ convexHull ℝ (Set.range v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterObservableExpectation.attention_mem_convexHull`.

-- Generated from ChapterObservableExpectation.lean — theorem BookProof.ChapterObservableExpectation.attention_mem_convexHull
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

theorem BookProof.ChapterObservableExpectation.attention_mem_convexHull (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (j₀ : Fin m) :
    attentionOutput q k v ∈ convexHull ℝ (Set.range v) := by sorry

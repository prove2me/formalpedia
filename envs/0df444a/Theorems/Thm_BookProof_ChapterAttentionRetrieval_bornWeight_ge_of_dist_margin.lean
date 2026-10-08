-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionRetrieval_bornWeight_ge_of_dist_margin
-- name    : BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:44:04.511984+00:00
-- url     : https://prove2.me/theorems/e0786a6b-c90b-43ce-98d9-ddcf62a27b3a
-- title:
--   `BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin` {delta : ℝ} (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) (hmargin : ∀ l, l ≠
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionRetrieval`.
--
--   `BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin` {delta : ℝ} (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) (hmargin : ∀ l, l ≠ j → ‖q - k j‖ ^ 2 + delta ≤ ‖q - k l‖ ^ 2) : 1 - ((m : ℝ) - 1) * Real.exp (-delta) ≤ bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin`.

-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin {delta : ℝ} (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    (hmargin : ∀ l, l ≠ j → ‖q - k j‖ ^ 2 + delta ≤ ‖q - k l‖ ^ 2) :
    1 - ((m : ℝ) - 1) * Real.exp (-delta) ≤ bornWeight q k j := by sorry

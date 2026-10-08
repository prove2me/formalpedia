-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionOutput_attentionOutput_eq_headOutput
-- name    : BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:34:19.185371+00:00
-- url     : https://prove2.me/theorems/1377f69f-9c16-4ea8-a278-e267ab2b4a6a
-- title:
--   `BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (r : ℝ) (hnorm : ∀ l, ‖k l‖ =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionOutput`.
--
--   `BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (r : ℝ) (hnorm : ∀ l, ‖k l‖ = r) : attentionOutput q k v = headOutput 2 (fun l => (inner ℝ q (k l) : ℝ)) v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput`.

-- Generated from ChapterAttentionOutput.lean — theorem BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterObservableExpectation
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionOutput


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionOutput.attentionOutput_eq_headOutput (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (v : Fin m → E) (r : ℝ)
    (hnorm : ∀ l, ‖k l‖ = r) :
    attentionOutput q k v = headOutput 2 (fun l => (inner ℝ q (k l) : ℝ)) v := by sorry

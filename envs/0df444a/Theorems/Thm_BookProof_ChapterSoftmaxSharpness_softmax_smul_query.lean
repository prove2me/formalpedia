-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_smul_query
-- name    : BookProof.ChapterSoftmaxSharpness.softmax_smul_query
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:07.3179+00:00
-- url     : https://prove2.me/theorems/dcaeb137-9ac3-4b9b-944b-d65d86d5bf8f
-- title:
--   `BookProof.ChapterSoftmaxSharpness.softmax_smul_query` (beta c : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : softmax beta (c • q) k j = s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.softmax_smul_query` (beta c : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : softmax beta (c • q) k j = softmax (beta * c) q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.softmax_smul_query`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.softmax_smul_query
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.softmax_smul_query (beta c : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    softmax beta (c • q) k j = softmax (beta * c) q k j := by sorry

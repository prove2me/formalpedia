-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxSharpness_ampBorn_smul_query
-- name    : BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T14:37:02.386413+00:00
-- url     : https://prove2.me/theorems/b82e9b82-55ca-4110-8f44-6a6cd3e18949
-- title:
--   `BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query` (c : ℝ) (hc : c ≠ 0) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : ampBorn (c • q) k j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxSharpness`.
--
--   `BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query` (c : ℝ) (hc : c ≠ 0) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : ampBorn (c • q) k j = ampBorn q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query`.

-- Generated from ChapterSoftmaxSharpness.lean — theorem BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query
import Definitions.Def_ChapterSoftmaxBorn
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxSharpness


open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxSharpness.ampBorn_smul_query (c : ℝ) (hc : c ≠ 0) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    ampBorn (c • q) k j = ampBorn q k j := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_bornDenom_pos
-- name    : BookProof.ChapterSoftmaxBorn.bornDenom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:27:33.420978+00:00
-- url     : https://prove2.me/theorems/9deaa4db-dada-41b7-8796-9b22aa2249a6
-- title:
--   `BookProof.ChapterSoftmaxBorn.bornDenom_pos` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < ∑ i, bornNumer q (k i)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.bornDenom_pos` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < ∑ i, bornNumer q (k i)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.bornDenom_pos`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.bornDenom_pos
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.bornDenom_pos (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n))
    (j : Fin m) : 0 < ∑ i, bornNumer q (k i) := by sorry

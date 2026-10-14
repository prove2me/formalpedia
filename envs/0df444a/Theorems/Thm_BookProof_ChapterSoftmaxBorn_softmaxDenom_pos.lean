-- Prove2me | Theorems.Thm_BookProof_ChapterSoftmaxBorn_softmaxDenom_pos
-- name    : BookProof.ChapterSoftmaxBorn.softmaxDenom_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:30.969852+00:00
-- url     : https://prove2.me/theorems/17acb40e-b361-4f7b-ab46-fee07a08109d
-- title:
--   `BookProof.ChapterSoftmaxBorn.softmaxDenom_pos` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < ∑ l, Real.exp (beta * inner ℝ q (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSoftmaxBorn`.
--
--   `BookProof.ChapterSoftmaxBorn.softmaxDenom_pos` (beta : ℝ) (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : 0 < ∑ l, Real.exp (beta * inner ℝ q (k l))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSoftmaxBorn.softmaxDenom_pos`.

-- Generated from ChapterSoftmaxBorn.lean — theorem BookProof.ChapterSoftmaxBorn.softmaxDenom_pos
import Definitions.Def_ChapterCoherentOverlap
import Mathlib
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlap

variable {n m : ℕ}

theorem BookProof.ChapterSoftmaxBorn.softmaxDenom_pos (beta : ℝ) (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    0 < ∑ l, Real.exp (beta * inner ℝ q (k l)) := by sorry

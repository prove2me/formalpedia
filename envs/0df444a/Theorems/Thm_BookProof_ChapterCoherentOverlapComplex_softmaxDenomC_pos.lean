-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_softmaxDenomC_pos
-- name    : BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:08.295003+00:00
-- url     : https://prove2.me/theorems/62d7da25-d9f2-48c9-af6e-f9d1f47f41c0
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos` (beta : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 < ∑ l, Real.exp (beta *
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos` (beta : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : 0 < ∑ l, Real.exp (beta * (inner ℂ q (k l) : ℂ).re)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.softmaxDenomC_pos (beta : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    0 < ∑ l, Real.exp (beta * (inner ℂ q (k l) : ℂ).re) := by sorry

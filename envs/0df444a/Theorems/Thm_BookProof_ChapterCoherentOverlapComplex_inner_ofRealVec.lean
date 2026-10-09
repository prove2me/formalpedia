-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_inner_ofRealVec
-- name    : BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:01:31.534099+00:00
-- url     : https://prove2.me/theorems/c204bdb9-237b-4e53-b4e2-5e2b559e096a
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec` (q k : EuclideanSpace ℝ (Fin n)) : inner ℂ (ofRealVec q) (ofRealVec k) = ((inner ℝ q k : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec` (q k : EuclideanSpace ℝ (Fin n)) : inner ℂ (ofRealVec q) (ofRealVec k) = ((inner ℝ q k : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.inner_ofRealVec (q k : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (ofRealVec q) (ofRealVec k) = ((inner ℝ q k : ℝ) : ℂ) := by sorry

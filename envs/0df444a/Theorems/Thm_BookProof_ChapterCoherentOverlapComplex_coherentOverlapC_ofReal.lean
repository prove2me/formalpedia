-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_coherentOverlapC_ofReal
-- name    : BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:01:39.413978+00:00
-- url     : https://prove2.me/theorems/645c50d1-e530-4d08-ae4a-6378cb939c2d
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlapC (ofRealVec q) (ofRealVec k) = ((BookProof.ChapterCoherentOverl
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : coherentOverlapC (ofRealVec q) (ofRealVec k) = ((BookProof.ChapterCoherentOverlap.coherentOverlap q k : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.coherentOverlapC_ofReal (q k : EuclideanSpace ℝ (Fin n)) :
    coherentOverlapC (ofRealVec q) (ofRealVec k)
      = ((BookProof.ChapterCoherentOverlap.coherentOverlap q k : ℝ) : ℂ) := by sorry

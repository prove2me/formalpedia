-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornNumerC_ofReal
-- name    : BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:02:13.403344+00:00
-- url     : https://prove2.me/theorems/d0ed1409-82f4-4aad-9be3-0fa35e164e1a
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : bornNumerC (ofRealVec q) (ofRealVec k) = BookProof.ChapterSoftmaxBorn.bornNumer q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal` (q k : EuclideanSpace ℝ (Fin n)) : bornNumerC (ofRealVec q) (ofRealVec k) = BookProof.ChapterSoftmaxBorn.bornNumer q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterCoherentOverlap
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.bornNumerC_ofReal (q k : EuclideanSpace ℝ (Fin n)) :
    bornNumerC (ofRealVec q) (ofRealVec k)
      = BookProof.ChapterSoftmaxBorn.bornNumer q k := by sorry

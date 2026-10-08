-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentOverlapComplex_bornWeightC_ofReal
-- name    : BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:03:01.340578+00:00
-- url     : https://prove2.me/theorems/48263557-a2c6-4463-87c9-98dc35cf20c5
-- title:
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeightC (ofRealVec q) (fun l =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentOverlapComplex`.
--
--   `BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal` (q : EuclideanSpace ℝ (Fin n)) (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) : bornWeightC (ofRealVec q) (fun l => ofRealVec (k l)) j = BookProof.ChapterSoftmaxBorn.bornWeight q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal`.

-- Generated from ChapterCoherentOverlapComplex.lean — theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal
import Mathlib
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterCoherentOverlapComplex


open scoped BigOperators

noncomputable section


variable {n m : ℕ}

theorem BookProof.ChapterCoherentOverlapComplex.bornWeightC_ofReal (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    bornWeightC (ofRealVec q) (fun l => ofRealVec (k l)) j
      = BookProof.ChapterSoftmaxBorn.bornWeight q k j := by sorry

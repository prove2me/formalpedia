-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornWeightC_isometry
-- name    : BookProof.ChapterCoherentDynamics.bornWeightC_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:17.200989+00:00
-- url     : https://prove2.me/theorems/652b602a-07af-430a-b11c-d80b5b9c5b1c
-- title:
--   `BookProof.ChapterCoherentDynamics.bornWeightC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornWeightC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (U q) (fun l => U (k l)) j = bornWeightC q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornWeightC_isometry`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornWeightC_isometry
import Definitions.Def_ChapterCoherentFidelity
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
import Definitions.Def_ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentOverlapComplex
open BookProof.ChapterCoherentDynamics


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

theorem BookProof.ChapterCoherentDynamics.bornWeightC_isometry (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (U q) (fun l => U (k l)) j = bornWeightC q k j := by sorry

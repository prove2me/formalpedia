-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornNumerC_isometry
-- name    : BookProof.ChapterCoherentDynamics.bornNumerC_isometry
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:11.061988+00:00
-- url     : https://prove2.me/theorems/d52fe2ea-4e5b-4b0a-8884-1e89977b7742
-- title:
--   `BookProof.ChapterCoherentDynamics.bornNumerC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (U q) (U k) = b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornNumerC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (U q) (U k) = bornNumerC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornNumerC_isometry`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornNumerC_isometry
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

theorem BookProof.ChapterCoherentDynamics.bornNumerC_isometry (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (U q) (U k) = bornNumerC q k := by sorry

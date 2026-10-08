-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_coherentOverlapC_isometry
-- name    : BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:47:51.104985+00:00
-- url     : https://prove2.me/theorems/ebfaa2b8-4507-4e22-ab07-27bcf23b76a7
-- title:
--   `BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry` (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (U q) (U k) = coherentOverlapC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
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

theorem BookProof.ChapterCoherentDynamics.coherentOverlapC_isometry
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC (U q) (U k) = coherentOverlapC q k := by sorry

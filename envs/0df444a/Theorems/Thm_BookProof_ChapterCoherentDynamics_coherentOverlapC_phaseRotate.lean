-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_coherentOverlapC_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:20.100144+00:00
-- url     : https://prove2.me/theorems/3a527607-0c20-4b19-b5e3-f250891ae598
-- title:
--   `BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (phaseRotate theta q) (phaseRotate theta k) = coher
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : coherentOverlapC (phaseRotate theta q) (phaseRotate theta k) = coherentOverlapC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate
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

theorem BookProof.ChapterCoherentDynamics.coherentOverlapC_phaseRotate (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    coherentOverlapC (phaseRotate theta q) (phaseRotate theta k) = coherentOverlapC q k := by sorry

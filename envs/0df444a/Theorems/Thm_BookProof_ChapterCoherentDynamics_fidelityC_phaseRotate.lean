-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_fidelityC_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:59.882447+00:00
-- url     : https://prove2.me/theorems/3649b3d4-2c84-42de-ad15-5b0ba87989c7
-- title:
--   `BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : fidelityC (phaseRotate theta q) (phaseRotate theta k) = fidelityC q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : fidelityC (phaseRotate theta q) (phaseRotate theta k) = fidelityC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate
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

theorem BookProof.ChapterCoherentDynamics.fidelityC_phaseRotate (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    fidelityC (phaseRotate theta q) (phaseRotate theta k) = fidelityC q k := by sorry

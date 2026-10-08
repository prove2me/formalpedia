-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornNumerC_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:50.797179+00:00
-- url     : https://prove2.me/theorems/186d2e3e-4a7f-44a8-b132-81e19b0d36d6
-- title:
--   `BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (phaseRotate theta q) (phaseRotate theta k) = bornNumerC q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : bornNumerC (phaseRotate theta q) (phaseRotate theta k) = bornNumerC q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate
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

theorem BookProof.ChapterCoherentDynamics.bornNumerC_phaseRotate (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    bornNumerC (phaseRotate theta q) (phaseRotate theta k) = bornNumerC q k := by sorry

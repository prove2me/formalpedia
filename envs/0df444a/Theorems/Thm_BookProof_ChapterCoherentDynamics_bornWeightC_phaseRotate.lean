-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornWeightC_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:50:40.402099+00:00
-- url     : https://prove2.me/theorems/e6dcb01b-b18e-4e71-8a7e-93298a4517c8
-- title:
--   `BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate` (theta : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (phaseRotate
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate` (theta : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (phaseRotate theta q) (fun l => phaseRotate theta (k l)) j = bornWeightC q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate
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

theorem BookProof.ChapterCoherentDynamics.bornWeightC_phaseRotate (theta : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (phaseRotate theta q) (fun l => phaseRotate theta (k l)) j
      = bornWeightC q k j := by sorry

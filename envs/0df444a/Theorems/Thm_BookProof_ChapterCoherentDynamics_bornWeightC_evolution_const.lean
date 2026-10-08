-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornWeightC_evolution_const
-- name    : BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:49:22.389757+00:00
-- url     : https://prove2.me/theorems/3f0f4774-0dec-42bc-b983-e134917aded8
-- title:
--   `BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const` (omega : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) (t : ℝ) : bornWeightC
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const` (omega : ℝ) (q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) (t : ℝ) : bornWeightC (phaseRotate (-(omega * t)) q) (fun l => phaseRotate (-(omega * t)) (k l)) j = bornWeightC q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const
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

theorem BookProof.ChapterCoherentDynamics.bornWeightC_evolution_const (omega : ℝ) (q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) (t : ℝ) :
    bornWeightC (phaseRotate (-(omega * t)) q)
        (fun l => phaseRotate (-(omega * t)) (k l)) j
      = bornWeightC q k j := by sorry

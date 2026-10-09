-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_bornWeightC_translation_invariant
-- name    : BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:49:19.958348+00:00
-- url     : https://prove2.me/theorems/71a2dea7-5c46-41e8-925b-1b7998778108
-- title:
--   `BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant` (v q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (q + v) (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant` (v q : EuclideanSpace ℂ (Fin n)) (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) : bornWeightC (q + v) (fun l => k l + v) j = bornWeightC q k j
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant
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

theorem BookProof.ChapterCoherentDynamics.bornWeightC_translation_invariant (v q : EuclideanSpace ℂ (Fin n))
    (k : Fin m → EuclideanSpace ℂ (Fin n)) (j : Fin m) :
    bornWeightC (q + v) (fun l => k l + v) j = bornWeightC q k j := by sorry

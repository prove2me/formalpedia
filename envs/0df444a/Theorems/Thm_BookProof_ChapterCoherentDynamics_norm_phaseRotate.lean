-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_norm_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.norm_phaseRotate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:48:14.878102+00:00
-- url     : https://prove2.me/theorems/1cc39be1-2456-4c13-aa8a-12a5b88594e7
-- title:
--   `BookProof.ChapterCoherentDynamics.norm_phaseRotate` (theta : ℝ) (q : EuclideanSpace ℂ (Fin n)) : ‖phaseRotate theta q‖ = ‖q‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.norm_phaseRotate` (theta : ℝ) (q : EuclideanSpace ℂ (Fin n)) : ‖phaseRotate theta q‖ = ‖q‖
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.norm_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.norm_phaseRotate
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterCoherentFidelity
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
open BookProof.ChapterCoherentDynamics


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

theorem BookProof.ChapterCoherentDynamics.norm_phaseRotate (theta : ℝ) (q : EuclideanSpace ℂ (Fin n)) :
    ‖phaseRotate theta q‖ = ‖q‖ := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterCoherentDynamics_inner_phaseRotate
-- name    : BookProof.ChapterCoherentDynamics.inner_phaseRotate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:49:19.542228+00:00
-- url     : https://prove2.me/theorems/18118ec3-0665-48d5-9913-3b889bd6a7c8
-- title:
--   `BookProof.ChapterCoherentDynamics.inner_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (phaseRotate theta q) (phaseRotate theta k) : ℂ) = inner ℂ q k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCoherentDynamics`.
--
--   `BookProof.ChapterCoherentDynamics.inner_phaseRotate` (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) : (inner ℂ (phaseRotate theta q) (phaseRotate theta k) : ℂ) = inner ℂ q k
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCoherentDynamics.inner_phaseRotate`.

-- Generated from ChapterCoherentDynamics.lean — theorem BookProof.ChapterCoherentDynamics.inner_phaseRotate
import Definitions.Def_ChapterCoherentOverlapComplex
import Definitions.Def_ChapterCoherentFidelity
import Mathlib
import Definitions.Def_ChapterCoherentDynamics
open BookProof.ChapterCoherentDynamics


open scoped BigOperators

noncomputable section


open BookProof.ChapterCoherentOverlapComplex BookProof.ChapterCoherentFidelity

variable {n m : ℕ}

theorem BookProof.ChapterCoherentDynamics.inner_phaseRotate (theta : ℝ) (q k : EuclideanSpace ℂ (Fin n)) :
    (inner ℂ (phaseRotate theta q) (phaseRotate theta k) : ℂ) = inner ℂ q k := by sorry

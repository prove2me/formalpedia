-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_quartA_single_confAt
-- name    : BookProof.FockCubicUnbounded.quartA_single_confAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:35:11.447527+00:00
-- url     : https://prove2.me/theorems/9c123749-fe8b-4349-92e2-6eabfe62781c
-- title:
--   `BookProof.FockCubicUnbounded.quartA_single_confAt` (k m : ℕ) (z : ℂ) : quartA k (Finsupp.single (confAt k m) z) = Finsupp.single (confAt k m) ((((m : ℝ) * ((m : ℝ) - 1) : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.quartA_single_confAt` (k m : ℕ) (z : ℂ) : quartA k (Finsupp.single (confAt k m) z) = Finsupp.single (confAt k m) ((((m : ℝ) * ((m : ℝ) - 1) : ℝ) : ℂ) * z)
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.quartA_single_confAt`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.quartA_single_confAt
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.quartA_single_confAt (k m : ℕ) (z : ℂ) :
    quartA k (Finsupp.single (confAt k m) z)
      = Finsupp.single (confAt k m) ((((m : ℝ) * ((m : ℝ) - 1) : ℝ) : ℂ) * z) := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_dn_confAt
-- name    : BookProof.FockCubicUnbounded.dn_confAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:33:34.364367+00:00
-- url     : https://prove2.me/theorems/19ab0209-4f09-4f90-be0e-76aff75f3430
-- title:
--   `BookProof.FockCubicUnbounded.dn_confAt` (k m : ℕ) : dn k (confAt k m) = confAt k (m - 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.dn_confAt` (k m : ℕ) : dn k (confAt k m) = confAt k (m - 1)
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.dn_confAt`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.dn_confAt
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

theorem BookProof.FockCubicUnbounded.dn_confAt (k m : ℕ) : dn k (confAt k m) = confAt k (m - 1) := by sorry

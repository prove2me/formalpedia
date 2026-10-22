-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_confAt_self
-- name    : BookProof.FockCubicUnbounded.confAt_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:32:58.035876+00:00
-- url     : https://prove2.me/theorems/49af9a1c-3a0d-4477-a180-aefb9e7c11e4
-- title:
--   `BookProof.FockCubicUnbounded.confAt_self` (k m : ℕ) : confAt k m k = m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.confAt_self` (k m : ℕ) : confAt k m k = m
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.confAt_self`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.confAt_self
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

theorem BookProof.FockCubicUnbounded.confAt_self (k m : ℕ) : confAt k m k = m := by sorry

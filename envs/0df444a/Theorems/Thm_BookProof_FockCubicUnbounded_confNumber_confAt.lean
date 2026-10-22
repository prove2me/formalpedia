-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_confNumber_confAt
-- name    : BookProof.FockCubicUnbounded.confNumber_confAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:33:12.960135+00:00
-- url     : https://prove2.me/theorems/cdcb1a7a-e841-425f-a240-54787b690610
-- title:
--   `BookProof.FockCubicUnbounded.confNumber_confAt` (k m : ℕ) : confNumber (confAt k m) = m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.confNumber_confAt` (k m : ℕ) : confNumber (confAt k m) = m
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.confNumber_confAt`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.confNumber_confAt
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.confNumber_confAt (k m : ℕ) : confNumber (confAt k m) = m := by sorry

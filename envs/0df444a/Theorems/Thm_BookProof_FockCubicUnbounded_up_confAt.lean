-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_up_confAt
-- name    : BookProof.FockCubicUnbounded.up_confAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:33:25.705991+00:00
-- url     : https://prove2.me/theorems/7053464a-0574-469c-bd46-47bbdc9710a9
-- title:
--   `BookProof.FockCubicUnbounded.up_confAt` (k m : ℕ) : up k (confAt k m) = confAt k (m + 1)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.up_confAt` (k m : ℕ) : up k (confAt k m) = confAt k (m + 1)
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.up_confAt`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.up_confAt
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

theorem BookProof.FockCubicUnbounded.up_confAt (k m : ℕ) : up k (confAt k m) = confAt k (m + 1) := by sorry

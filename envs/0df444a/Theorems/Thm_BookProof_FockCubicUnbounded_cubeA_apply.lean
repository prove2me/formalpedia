-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_cubeA_apply
-- name    : BookProof.FockCubicUnbounded.cubeA_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:33:14.384988+00:00
-- url     : https://prove2.me/theorems/8b67897a-4a64-47ae-80a7-31b4a86b06e8
-- title:
--   `BookProof.FockCubicUnbounded.cubeA_apply` (k : ℕ) (x : FockAlg) : cubeA k x = creA k (creA k (creA k x)) + annA k (annA k (annA k x))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.cubeA_apply` (k : ℕ) (x : FockAlg) : cubeA k x = creA k (creA k (creA k x)) + annA k (annA k (annA k x))
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.cubeA_apply`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.cubeA_apply
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

theorem BookProof.FockCubicUnbounded.cubeA_apply (k : ℕ) (x : FockAlg) :
    cubeA k x = creA k (creA k (creA k x)) + annA k (annA k (annA k x)) := by sorry

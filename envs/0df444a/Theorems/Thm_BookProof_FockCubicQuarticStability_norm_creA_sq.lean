-- Prove2me | Theorems.Thm_BookProof_FockCubicQuarticStability_norm_creA_sq
-- name    : BookProof.FockCubicQuarticStability.norm_creA_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:46:58.016992+00:00
-- url     : https://prove2.me/theorems/7b7f017c-f510-4b4d-8b09-9f21046d2777
-- title:
--   `BookProof.FockCubicQuarticStability.norm_creA_sq` (k : ℕ) (v : FockAlg) : ‖toLp (creA k v)‖ ^ 2 = ‖toLp (annA k v)‖ ^ 2 + ‖toLp v‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicQuarticStability`.
--
--   `BookProof.FockCubicQuarticStability.norm_creA_sq` (k : ℕ) (v : FockAlg) : ‖toLp (creA k v)‖ ^ 2 = ‖toLp (annA k v)‖ ^ 2 + ‖toLp v‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicQuarticStability.norm_creA_sq`.

-- Generated from ChapterFockCubicQuarticStability.lean — theorem BookProof.FockCubicQuarticStability.norm_creA_sq
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockCubicUnbounded
import Mathlib
import Definitions.Def_ChapterFockCubicQuarticStability
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockCubicQuarticStability


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockCubicUnbounded

theorem BookProof.FockCubicQuarticStability.norm_creA_sq (k : ℕ) (v : FockAlg) :
    ‖toLp (creA k v)‖ ^ 2 = ‖toLp (annA k v)‖ ^ 2 + ‖toLp v‖ ^ 2 := by sorry

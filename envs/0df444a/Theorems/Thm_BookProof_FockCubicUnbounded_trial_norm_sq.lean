-- Prove2me | Theorems.Thm_BookProof_FockCubicUnbounded_trial_norm_sq
-- name    : BookProof.FockCubicUnbounded.trial_norm_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-21T11:34:51.760605+00:00
-- url     : https://prove2.me/theorems/9ac16dc3-0719-4da6-975e-2ec76c7c2a0e
-- title:
--   `BookProof.FockCubicUnbounded.trial_norm_sq` (k n : ℕ) (c : ℝ) : ‖toLp (trial k n c)‖ ^ 2 = 1 + c ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockCubicUnbounded`.
--
--   `BookProof.FockCubicUnbounded.trial_norm_sq` (k n : ℕ) (c : ℝ) : ‖toLp (trial k n c)‖ ^ 2 = 1 + c ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockCubicUnbounded.trial_norm_sq`.

-- Generated from ChapterFockCubicUnbounded.lean — theorem BookProof.FockCubicUnbounded.trial_norm_sq
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTempleSeparationNecessary
open BookProof.FockSecondQuantization
open BookProof.TempleSeparationNecessary
open BookProof.FockCubicUnbounded


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation

theorem BookProof.FockCubicUnbounded.trial_norm_sq (k n : ℕ) (c : ℝ) : ‖toLp (trial k n c)‖ ^ 2 = 1 + c ^ 2 := by sorry

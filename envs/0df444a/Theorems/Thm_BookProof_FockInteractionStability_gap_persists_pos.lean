-- Prove2me | Theorems.Thm_BookProof_FockInteractionStability_gap_persists_pos
-- name    : BookProof.FockInteractionStability.gap_persists_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T10:11:32.598991+00:00
-- url     : https://prove2.me/theorems/cbd73d2b-4ae0-4484-befa-7d89f6a79e10
-- title:
--   `BookProof.FockInteractionStability.gap_persists_pos` {mu a b : ℝ} (hmu : 0 < mu) (ha : a < 1) (hb : b < (1 - a) * mu) : 0 < (1 - a) * mu - b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockInteractionStability`.
--
--   `BookProof.FockInteractionStability.gap_persists_pos` {mu a b : ℝ} (hmu : 0 < mu) (ha : a < 1) (hb : b < (1 - a) * mu) : 0 < (1 - a) * mu - b
--
--   Formalization note: Lean 4 identifier `BookProof.FockInteractionStability.gap_persists_pos`.

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.gap_persists_pos
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
open BookProof.FockInteractionStability

variable {E : Type*} [NormedAddCommGroup E]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockInteractionStability.gap_persists_pos {mu a b : ℝ} (hmu : 0 < mu) (ha : a < 1) (hb : b < (1 - a) * mu) :
    0 < (1 - a) * mu - b := by sorry

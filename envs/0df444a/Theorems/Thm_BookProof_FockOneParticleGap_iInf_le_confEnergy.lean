-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_iInf_le_confEnergy
-- name    : BookProof.FockOneParticleGap.iInf_le_confEnergy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:10:28.434022+00:00
-- url     : https://prove2.me/theorems/0e24de53-c58f-47de-b489-bcc6c8dd7b70
-- title:
--   {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) {β : Conf} (hβ : β ≠ 0) : (⨅ k, e k) ≤ confEnergy e β
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.iInf_le_confEnergy` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.iInf_le_confEnergy
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.iInf_le_confEnergy {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) {β : Conf} (hβ : β ≠ 0) :
    (⨅ k, e k) ≤ confEnergy e β := by sorry

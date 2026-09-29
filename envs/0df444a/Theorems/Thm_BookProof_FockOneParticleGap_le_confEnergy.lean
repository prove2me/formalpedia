-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_le_confEnergy
-- name    : BookProof.FockOneParticleGap.le_confEnergy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:52:53.384232+00:00
-- url     : https://prove2.me/theorems/606615e1-98a5-4cfa-bb38-834dad2bac83
-- title:
--   {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k) {β : Conf} (hβ : β ≠ 0) : mu ≤ confEnergy e β
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.le_confEnergy` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.le_confEnergy
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.le_confEnergy {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k)
    {β : Conf} (hβ : β ≠ 0) : mu ≤ confEnergy e β := by sorry

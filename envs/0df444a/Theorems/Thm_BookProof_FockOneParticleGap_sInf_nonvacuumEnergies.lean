-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_sInf_nonvacuumEnergies
-- name    : BookProof.FockOneParticleGap.sInf_nonvacuumEnergies
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:55:07.542584+00:00
-- url     : https://prove2.me/theorems/cef6e6a8-6b66-457e-abb8-f205e3efc8a3
-- title:
--   {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) : sInf (nonvacuumEnergies e) = ⨅ k, e k
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.sInf_nonvacuumEnergies` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.sInf_nonvacuumEnergies
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.sInf_nonvacuumEnergies {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) :
    sInf (nonvacuumEnergies e) = ⨅ k, e k := by sorry

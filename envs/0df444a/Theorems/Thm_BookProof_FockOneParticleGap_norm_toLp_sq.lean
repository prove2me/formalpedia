-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_norm_toLp_sq
-- name    : BookProof.FockOneParticleGap.norm_toLp_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:53:32.759227+00:00
-- url     : https://prove2.me/theorems/7f6d4067-8579-4a28-8d64-7215c89a24d7
-- title:
--   (u : FockAlg) : ‖toLp u‖ ^ 2 = ∑ α ∈ u.support, ‖u α‖ ^ 2
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.norm_toLp_sq` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.norm_toLp_sq
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.norm_toLp_sq (u : FockAlg) : ‖toLp u‖ ^ 2 = ∑ α ∈ u.support, ‖u α‖ ^ 2 := by sorry

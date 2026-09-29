-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_inner_vac
-- name    : BookProof.FockOneParticleGap.inner_vac
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:11:09.862189+00:00
-- url     : https://prove2.me/theorems/f8bd13e0-afe1-47c2-85d7-b472e979552c
-- title:
--   (u : FockAlg) : (inner ℂ (toLp vac) (toLp u) : ℂ) = u 0
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.inner_vac` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.inner_vac
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.inner_vac (u : FockAlg) : (inner ℂ (toLp vac) (toLp u) : ℂ) = u 0 := by sorry

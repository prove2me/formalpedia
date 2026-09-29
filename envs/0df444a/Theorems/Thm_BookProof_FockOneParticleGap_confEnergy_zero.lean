-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_zero
-- name    : BookProof.FockOneParticleGap.confEnergy_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:06:41.865352+00:00
-- url     : https://prove2.me/theorems/c5b9a61f-2dde-4317-acda-758d37b8c164
-- title:
--   (e : ℕ → ℝ) : confEnergy e (0 : Conf) = 0
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.confEnergy_zero` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.confEnergy_zero
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.confEnergy_zero (e : ℕ → ℝ) : confEnergy e (0 : Conf) = 0 := by sorry

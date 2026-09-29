-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_single
-- name    : BookProof.FockOneParticleGap.confEnergy_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:06:07.13474+00:00
-- url     : https://prove2.me/theorems/4b6683d5-65cf-49fa-a92e-10b07e00bd17
-- title:
--   (e : ℕ → ℝ) (k : ℕ) : confEnergy e (Finsupp.single k 1) = e k
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.confEnergy_single` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.confEnergy_single
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.confEnergy_single (e : ℕ → ℝ) (k : ℕ) :
    confEnergy e (Finsupp.single k 1) = e k := by sorry

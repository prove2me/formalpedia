-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_confEnergy_add_const
-- name    : BookProof.FockOneParticleGap.confEnergy_add_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:04:12.135093+00:00
-- url     : https://prove2.me/theorems/7187de68-fb56-412e-ab4a-90451f5310dc
-- title:
--   (e : ℕ → ℝ) (mu : ℝ) (β : Conf) : confEnergy (fun k => e k + mu) β = confEnergy e β + mu * (confNumber β : ℝ)
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.confEnergy_add_const` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.confEnergy_add_const
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.confEnergy_add_const (e : ℕ → ℝ) (mu : ℝ) (β : Conf) :
    confEnergy (fun k => e k + mu) β = confEnergy e β + mu * (confNumber β : ℝ) := by sorry

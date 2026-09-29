-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_apply
-- name    : BookProof.FockOneParticleGap.dGamma_diagCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:54:38.536905+00:00
-- url     : https://prove2.me/theorems/8b8c7b66-165b-4e13-8f4d-4a7fedefd369
-- title:
--   (e : ℕ → ℝ) (u : FockAlg) (β : Conf) : dGamma (diagCol e) u β = ((confEnergy e β : ℝ) : ℂ) * u β
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.dGamma_diagCol_apply` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.dGamma_diagCol_apply
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.dGamma_diagCol_apply (e : ℕ → ℝ) (u : FockAlg) (β : Conf) :
    dGamma (diagCol e) u β = ((confEnergy e β : ℝ) : ℂ) * u β := by sorry

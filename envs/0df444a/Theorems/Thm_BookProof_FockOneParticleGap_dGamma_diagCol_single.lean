-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_single
-- name    : BookProof.FockOneParticleGap.dGamma_diagCol_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:54:19.700509+00:00
-- url     : https://prove2.me/theorems/0679ec01-6307-4ec3-b18a-c0c71d6fdd42
-- title:
--   (e : ℕ → ℝ) (β : Conf) (c : ℂ) : dGamma (diagCol e) (Finsupp.single β c) = ((confEnergy e β : ℝ) : ℂ) • Finsupp.single β c
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.dGamma_diagCol_single` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.dGamma_diagCol_single
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.dGamma_diagCol_single (e : ℕ → ℝ) (β : Conf) (c : ℂ) :
    dGamma (diagCol e) (Finsupp.single β c)
      = ((confEnergy e β : ℝ) : ℂ) • Finsupp.single β c := by sorry

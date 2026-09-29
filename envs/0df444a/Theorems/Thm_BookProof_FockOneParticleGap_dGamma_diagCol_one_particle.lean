-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_one_particle
-- name    : BookProof.FockOneParticleGap.dGamma_diagCol_one_particle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:55:22.466705+00:00
-- url     : https://prove2.me/theorems/f4dca5ec-4122-447c-8f65-a42627f97a7f
-- title:
--   (e : ℕ → ℝ) (k : ℕ) : dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)) = ((e k : ℝ) : ℂ) • Finsupp.single (Finsupp.single k 1) (1 : ℂ)
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.dGamma_diagCol_one_particle` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.dGamma_diagCol_one_particle
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.dGamma_diagCol_one_particle (e : ℕ → ℝ) (k : ℕ) :
    dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ))
      = ((e k : ℝ) : ℂ) • Finsupp.single (Finsupp.single k 1) (1 : ℂ) := by sorry

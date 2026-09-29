-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_fock_energy_one_particle
-- name    : BookProof.FockOneParticleGap.fock_energy_one_particle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:13:51.140604+00:00
-- url     : https://prove2.me/theorems/76e598ea-1406-4683-bde0-201b26995525
-- title:
--   (e : ℕ → ℝ) (k : ℕ) : (inner ℂ (toLp (Finsupp.single (Finsupp.single k 1) (1 : ℂ))) (toLp (dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))) : ℂ).re = e k
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.fock_energy_one_particle` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.fock_energy_one_particle
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.fock_energy_one_particle (e : ℕ → ℝ) (k : ℕ) :
    (inner ℂ (toLp (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))
        (toLp (dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))) : ℂ).re
      = e k := by sorry

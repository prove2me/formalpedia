-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_of_one_particle_gap
-- name    : BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:14:28.379014+00:00
-- url     : https://prove2.me/theorems/2e458d34-c83b-4c4c-9a45-0023b6b2dfb5
-- title:
--   {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k) : dGammaOp (diagCol e) (fockEquiv vac) = 0 ∧ ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →...
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (he : ∀ k, mu ≤ e k) :
    dGammaOp (diagCol e) (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp (diagCol e)) x := by sorry

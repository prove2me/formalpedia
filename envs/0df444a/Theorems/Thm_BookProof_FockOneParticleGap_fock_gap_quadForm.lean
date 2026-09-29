-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
-- name    : BookProof.FockOneParticleGap.fock_gap_quadForm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:14:13.135414+00:00
-- url     : https://prove2.me/theorems/bd060d08-2061-4f4a-aa36-7888bd9ed40d
-- title:
--   {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k) {u : FockAlg} (h0 : u 0 = 0) : mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.fock_gap_quadForm` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.fock_gap_quadForm
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

theorem BookProof.FockOneParticleGap.fock_gap_quadForm {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k)
    {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by sorry

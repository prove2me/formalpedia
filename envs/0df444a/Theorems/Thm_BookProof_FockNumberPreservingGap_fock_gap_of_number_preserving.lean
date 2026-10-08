-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_number_preserving
-- name    : BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:39:35.335902+00:00
-- url     : https://prove2.me/theorems/76b61b3a-39ac-471f-9912-8579bb2fb7c9
-- title:
--   `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) {u : FockAlg} (h0 : u 0 = 0) : mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) {u : FockAlg} (h0 : u 0 = 0) : mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by sorry

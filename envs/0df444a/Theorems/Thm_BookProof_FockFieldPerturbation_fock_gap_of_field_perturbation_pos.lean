-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_fock_gap_of_field_perturbation_pos
-- name    : BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:36:11.633692+00:00
-- url     : https://prove2.me/theorems/f36d5739-e514-47c7-a361-d9a12e611712
-- title:
--   `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu) (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : 2 *...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu) (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < mu) {u : FockAlg} (h0 : u 0 = 0) : 0 < mu - 2 * l2norm f ∧ (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability

theorem BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation_pos {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : 2 * l2norm f < mu)
    {u : FockAlg} (h0 : u 0 = 0) :
    0 < mu - 2 * l2norm f ∧
      (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2
        ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
          + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := by sorry

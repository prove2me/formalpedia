-- Prove2me | Theorems.Thm_BookProof_FockFieldPerturbation_fock_gap_of_field_perturbation
-- name    : BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:36:21.383542+00:00
-- url     : https://prove2.me/theorems/2569aeac-eef1-460f-b431-3164ccad14b2
-- title:
--   `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu) (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : l2norm...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockFieldPerturbation`.
--
--   `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation` {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu) (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : l2norm f ≤ mu) {u : FockAlg} (h0 : u 0 = 0) : (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation`.

-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation
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

theorem BookProof.FockFieldPerturbation.fock_gap_of_field_perturbation {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 < mu)
    (hgap : IsPosCol (shiftCol col mu)) {f : ℕ →₀ ℂ} (hf : l2norm f ≤ mu)
    {u : FockAlg} (h0 : u 0 = 0) :
    (mu - 2 * l2norm f) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + (inner ℂ (toLp u) (toLp (fieldVec f u)) : ℂ).re := by sorry

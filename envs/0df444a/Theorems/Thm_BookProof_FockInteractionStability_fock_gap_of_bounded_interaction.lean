-- Prove2me | Theorems.Thm_BookProof_FockInteractionStability_fock_gap_of_bounded_interaction
-- name    : BookProof.FockInteractionStability.fock_gap_of_bounded_interaction
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T11:42:14.553574+00:00
-- url     : https://prove2.me/theorems/f71a1445-79c7-4a6e-992f-a53c8ab389ac
-- title:
--   `BookProof.FockInteractionStability.fock_gap_of_bounded_interaction` {col : ℕ → (ℕ →₀ ℂ)} {mu delta : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) (V : Fock →L[ℂ] Fock) (h
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockInteractionStability`.
--
--   `BookProof.FockInteractionStability.fock_gap_of_bounded_interaction` {col : ℕ → (ℕ →₀ ℂ)} {mu delta : ℝ} (hmu : 0 ≤ mu) (hgap : IsPosCol (shiftCol col mu)) (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta) {u : FockAlg} (h0 : u 0 = 0) : (mu - delta) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockInteractionStability.fock_gap_of_bounded_interaction`.

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.fock_gap_of_bounded_interaction
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization
open BookProof.FockInteractionStability

variable {E : Type*} [NormedAddCommGroup E]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockInteractionStability.fock_gap_of_bounded_interaction {col : ℕ → (ℕ →₀ ℂ)} {mu delta : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta)
    {u : FockAlg} (h0 : u 0 = 0) :
    (mu - delta) * ‖toLp u‖ ^ 2
      ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re
        + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re := by sorry

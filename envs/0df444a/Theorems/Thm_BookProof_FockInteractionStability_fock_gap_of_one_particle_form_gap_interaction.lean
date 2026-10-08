-- Prove2me | Theorems.Thm_BookProof_FockInteractionStability_fock_gap_of_one_particle_form_gap_interaction
-- name    : BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-06T10:12:20.963275+00:00
-- url     : https://prove2.me/theorems/301f4a0d-8577-44c4-b469-08cac376e754
-- title:
--   `BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F) (A : BookProo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockInteractionStability`.
--
--   `BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction` {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F) (A : BookProof.HermiteGalerkin.finiteModeDomain b →ₗ[ℂ] BookProof.HermiteGalerkin.finiteModeDomain b) {mu delta : ℝ} (hmu : 0 ≤ mu) (hgap : ∀ x : BookProof.HermiteGalerkin.finiteModeDomain b, mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((BookProof.HermiteGalerkin.finiteModeDomain b).subtype.comp A) x) (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta) : dGamma (opCol b A) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → (mu - delta) * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction`.

-- Generated from ChapterFockInteractionStability.lean — theorem BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockInteractionStability
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.FockInteractionStability

variable {E : Type*} [NormedAddCommGroup E]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockInteractionStability.fock_gap_of_one_particle_form_gap_interaction
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F)
    (A : BookProof.HermiteGalerkin.finiteModeDomain b →ₗ[ℂ]
      BookProof.HermiteGalerkin.finiteModeDomain b)
    {mu delta : ℝ} (hmu : 0 ≤ mu)
    (hgap : ∀ x : BookProof.HermiteGalerkin.finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤
        quadForm ((BookProof.HermiteGalerkin.finiteModeDomain b).subtype.comp A) x)
    (V : Fock →L[ℂ] Fock) (hV : ‖V‖ ≤ delta) :
    dGamma (opCol b A) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (mu - delta) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re
            + (inner ℂ (toLp u) (V (toLp u)) : ℂ).re := by sorry

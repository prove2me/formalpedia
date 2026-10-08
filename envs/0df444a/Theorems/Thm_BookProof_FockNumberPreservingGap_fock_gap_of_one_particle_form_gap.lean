-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_one_particle_form_gap
-- name    : BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T20:46:31.228555+00:00
-- url     : https://prove2.me/theorems/5f7a3816-a8c3-435f-aa73-c828b3c59589
-- title:
--   `BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hmu : 0 ≤ mu) (hgap : ∀ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap` (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hmu : 0 ≤ mu) (hgap : ∀ x : finiteModeDomain b, mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) : dGamma (opCol b A) vac = 0 ∧ ∀ u : FockAlg, u 0 = 0 → mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.HermiteGalerkin
open BookProof.FockNumberPreservingGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.fock_gap_of_one_particle_form_gap (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : ∀ x : finiteModeDomain b,
      mu * ‖(x : F)‖ ^ 2 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    dGamma (opCol b A) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (opCol b A) u)) : ℂ).re := by sorry

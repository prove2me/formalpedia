-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_secondQuantization_friedrichs
-- name    : BookProof.FockSecondQuantization.secondQuantization_friedrichs
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:29:14.90746+00:00
-- url     : https://prove2.me/theorems/7fb7d08c-325e-4328-bc1b-cd7e7eb3a782
-- title:
--   (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A)) (hpos : ∀ x, 0 ≤ quadForm...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.secondQuantization_friedrichs` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.secondQuantization_friedrichs
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockSecondQuantization.secondQuantization_friedrichs (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (opCol b A)) A' := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_opCol_apply
-- name    : BookProof.FockSecondQuantization.opCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:57:03.521529+00:00
-- url     : https://prove2.me/theorems/ca1a6cbe-d460-4038-a2a6-e213df5f6549
-- title:
--   (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b) (k j : ℕ) : opCol b A k j = inner ℂ (b j) ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.opCol_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.opCol_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockSecondQuantization.opCol_apply (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (k j : ℕ) :
    opCol b A k j
      = inner ℂ (b j) ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F) := by sorry

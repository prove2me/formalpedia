-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_isHermCol_opCol
-- name    : BookProof.FockSecondQuantization.isHermCol_opCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:57:37.001168+00:00
-- url     : https://prove2.me/theorems/61a2d8d9-6a73-41a5-bb33-93fb052ee7ca
-- title:
--   {b : HilbertBasis ℕ ℂ F} {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b} (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A)) : IsHermCol (opCol b A)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.isHermCol_opCol` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.isHermCol_opCol
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockSecondQuantization.isHermCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A)) :
    IsHermCol (opCol b A) := by sorry

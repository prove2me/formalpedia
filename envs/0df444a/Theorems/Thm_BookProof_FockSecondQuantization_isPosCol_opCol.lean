-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_isPosCol_opCol
-- name    : BookProof.FockSecondQuantization.isPosCol_opCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:58:19.459141+00:00
-- url     : https://prove2.me/theorems/0db0a7ff-bed6-4ad0-ad5d-93e14b8c58af
-- title:
--   {b : HilbertBasis ℕ ℂ F} {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b} (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) : IsPosCol (opCol b A)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.isPosCol_opCol` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.isPosCol_opCol
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockSecondQuantization.isPosCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    IsPosCol (opCol b A) := by sorry

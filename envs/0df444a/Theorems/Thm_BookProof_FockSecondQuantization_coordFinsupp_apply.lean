-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_coordFinsupp_apply
-- name    : BookProof.FockSecondQuantization.coordFinsupp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:16:59.141127+00:00
-- url     : https://prove2.me/theorems/ffcca7f8-eee5-4c0b-989c-927726782b81
-- title:
--   {b : HilbertBasis ℕ ℂ F} {x : F} (hx : x ∈ finiteModeDomain b) (j : ℕ) : coordFinsupp b x j = inner ℂ (b j) x
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.coordFinsupp_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.coordFinsupp_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

















































































variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.FockSecondQuantization.coordFinsupp_apply {b : HilbertBasis ℕ ℂ F} {x : F} (hx : x ∈ finiteModeDomain b)
    (j : ℕ) : coordFinsupp b x j = inner ℂ (b j) x := by sorry

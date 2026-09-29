-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGamma_friedrichs_extension
-- name    : BookProof.FockSecondQuantization.dGamma_friedrichs_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:28:50.198847+00:00
-- url     : https://prove2.me/theorems/4808c4d7-9279-4cb7-b502-dc067219395a
-- title:
--   {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (hpos : IsPosCol col) : ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock), IsPositiveSelfAdjointExtension (dGammaOp col) A
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGamma_friedrichs_extension` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGamma_friedrichs_extension
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGamma_friedrichs_extension {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col)
    (hpos : IsPosCol col) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp col) A := by sorry

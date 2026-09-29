-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_symmetricOn
-- name    : BookProof.FockSecondQuantization.dGammaOp_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:24:46.095913+00:00
-- url     : https://prove2.me/theorems/69f9cd54-ce9e-4f19-8ae1-8f510c16a15e
-- title:
--   {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) : SymmetricOn (lpFiniteModes Conf) (dGammaOp col)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGammaOp_symmetricOn` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGammaOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGammaOp_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by sorry

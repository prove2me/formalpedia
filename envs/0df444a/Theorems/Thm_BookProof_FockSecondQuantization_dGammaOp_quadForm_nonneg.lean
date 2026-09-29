-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_dGammaOp_quadForm_nonneg
-- name    : BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:22:57.621645+00:00
-- url     : https://prove2.me/theorems/a588b556-f42c-4ba9-81df-ef585fcc8f39
-- title:
--   {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.dGammaOp_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x := by sorry

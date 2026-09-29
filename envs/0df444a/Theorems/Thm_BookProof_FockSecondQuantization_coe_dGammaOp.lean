-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
-- name    : BookProof.FockSecondQuantization.coe_dGammaOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:14:52.730671+00:00
-- url     : https://prove2.me/theorems/0292542d-6cf6-4c85-831a-42211af92426
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) : dGammaOp col x = toLp (dGamma col (fockEquiv.symm x))
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.coe_dGammaOp` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.coe_dGammaOp
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.coe_dGammaOp (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp col x = toLp (dGamma col (fockEquiv.symm x)) := by sorry

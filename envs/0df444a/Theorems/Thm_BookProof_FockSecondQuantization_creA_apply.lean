-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_creA_apply
-- name    : BookProof.FockSecondQuantization.creA_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:16:22.249197+00:00
-- url     : https://prove2.me/theorems/1a6b5940-940e-4088-99dd-c9a02626c41c
-- title:
--   (j : ℕ) (u : FockAlg) (α : Conf) : creA j u α = ((Real.sqrt (α j) : ℝ) : ℂ) * u (dn j α)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.creA_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.creA_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.creA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    creA j u α = ((Real.sqrt (α j) : ℝ) : ℂ) * u (dn j α) := by sorry

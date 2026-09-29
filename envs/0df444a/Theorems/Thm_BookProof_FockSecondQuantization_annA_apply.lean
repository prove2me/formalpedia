-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_annA_apply
-- name    : BookProof.FockSecondQuantization.annA_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:15:34.106955+00:00
-- url     : https://prove2.me/theorems/d0f53044-502f-4e68-97fa-46403b2187de
-- title:
--   (j : ℕ) (u : FockAlg) (α : Conf) : annA j u α = ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * u (up j α)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.annA_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.annA_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.annA_apply (j : ℕ) (u : FockAlg) (α : Conf) :
    annA j u α = ((Real.sqrt ((α j : ℝ) + 1) : ℝ) : ℂ) * u (up j α) := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
-- name    : BookProof.FockSecondQuantization.creVec_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:18:25.247428+00:00
-- url     : https://prove2.me/theorems/9ac84545-4e10-42ca-89cb-82ba87f3bcdb
-- title:
--   (v : ℕ →₀ ℂ) (x : FockAlg) : creVec v x = ∑ j ∈ v.support, v j • creA j x
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.creVec_apply` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.creVec_apply
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.creVec_apply (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec v x = ∑ j ∈ v.support, v j • creA j x := by sorry

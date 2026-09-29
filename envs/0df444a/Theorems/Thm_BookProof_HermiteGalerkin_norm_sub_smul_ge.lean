-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_norm_sub_smul_ge
-- name    : BookProof.HermiteGalerkin.norm_sub_smul_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:33:22.551217+00:00
-- url     : https://prove2.me/theorems/b9d0cab8-9708-4b0b-aa6c-2a9b0e2ed789
-- title:
--   The Lean 4 theorem `norm_sub_smul_ge` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sub_smul_ge` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.norm_sub_smul_ge
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.HermiteGalerkin.norm_sub_smul_ge (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) (z : ℂ) (u : F) :
    |z.im| * ‖u‖ ≤ ‖(algebraMap ℂ (F →L[ℂ] F) z - T) u‖ := by sorry

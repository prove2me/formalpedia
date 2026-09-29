-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_sub_resolvent_apply
-- name    : BookProof.HermiteGalerkin.sub_resolvent_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:09.785356+00:00
-- url     : https://prove2.me/theorems/acdfae94-37c2-4a62-8110-bc287f70df3f
-- title:
--   The Lean 4 theorem `sub_resolvent_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sub_resolvent_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.sub_resolvent_apply
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

theorem BookProof.HermiteGalerkin.sub_resolvent_apply (T : F →L[ℂ] F) (hT : IsSelfAdjoint T) {z : ℂ} (hz : z.im ≠ 0)
    (w : F) : (algebraMap ℂ (F →L[ℂ] F) z - T) (resolvent T z w) = w := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_ritzInf_extension_le
-- name    : BookProof.HermiteGalerkin.ritzInf_extension_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:29.793984+00:00
-- url     : https://prove2.me/theorems/06c08086-42a9-4ab5-a76c-e2b5df068226
-- title:
--   The Lean 4 theorem `ritzInf_extension_le` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritzInf_extension_le` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.ritzInf_extension_le
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}

theorem BookProof.HermiteGalerkin.ritzInf_extension_le {Dom : Submodule ℂ F} (H : D →ₗ[ℂ] F) (A : Dom →ₗ[ℂ] F)
    (hA : IsPositiveSelfAdjointExtension H A) (hne : (ritzSet H D).Nonempty) :
    ritzInf A Dom ≤ ritzInf H D := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_ritzSet_mono
-- name    : BookProof.HermiteGalerkin.ritzSet_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:44:24.362029+00:00
-- url     : https://prove2.me/theorems/adbaa30f-78ae-40c9-bae9-294753a738cf
-- title:
--   The Lean 4 theorem `ritzSet_mono` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritzSet_mono` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.ritzSet_mono
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}

theorem BookProof.HermiteGalerkin.ritzSet_mono (H : D →ₗ[ℂ] F) {V W : Submodule ℂ F} (hVW : V ≤ W) :
    ritzSet H V ⊆ ritzSet H W := by sorry

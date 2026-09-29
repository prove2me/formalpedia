-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_ritzSet_bddBelow
-- name    : BookProof.HermiteGalerkin.ritzSet_bddBelow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:44:02.842298+00:00
-- url     : https://prove2.me/theorems/3377884b-8aa4-4c8b-86a2-a91390697b6b
-- title:
--   The Lean 4 theorem `ritzSet_bddBelow` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ritzSet_bddBelow` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.ritzSet_bddBelow
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {D : Submodule ℂ F}

theorem BookProof.HermiteGalerkin.ritzSet_bddBelow (H : D →ₗ[ℂ] F) (hpos : ∀ x : D, 0 ≤ quadForm H x)
    (V : Submodule ℂ F) : BddBelow (ritzSet H V) := by sorry

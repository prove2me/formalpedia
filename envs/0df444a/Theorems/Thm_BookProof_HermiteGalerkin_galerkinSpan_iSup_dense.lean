-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_galerkinSpan_iSup_dense
-- name    : BookProof.HermiteGalerkin.galerkinSpan_iSup_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:17:17.524713+00:00
-- url     : https://prove2.me/theorems/6bbd9c8a-3556-436e-92fe-52dc240d4a66
-- title:
--   The Lean 4 theorem `galerkinSpan_iSup_dense` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinSpan_iSup_dense` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.galerkinSpan_iSup_dense
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.galerkinSpan_iSup_dense (b : HilbertBasis ℕ ℂ F) :
    Dense ((⨆ m : ℕ, galerkinSpan b m : Submodule ℂ F) : Set F) := by sorry

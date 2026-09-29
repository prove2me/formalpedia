-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_galerkinSpan_le_finiteModeDomain
-- name    : BookProof.HermiteGalerkin.galerkinSpan_le_finiteModeDomain
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:30:59.554346+00:00
-- url     : https://prove2.me/theorems/ae3e41ed-1ced-4d3c-bc7a-1db135d60d56
-- title:
--   The Lean 4 theorem `galerkinSpan_le_finiteModeDomain` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinSpan_le_finiteModeDomain` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.galerkinSpan_le_finiteModeDomain
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.galerkinSpan_le_finiteModeDomain (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    galerkinSpan b m ≤ finiteModeDomain b := by sorry

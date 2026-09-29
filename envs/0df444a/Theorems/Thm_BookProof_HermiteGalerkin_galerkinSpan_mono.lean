-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_galerkinSpan_mono
-- name    : BookProof.HermiteGalerkin.galerkinSpan_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:33:04.827045+00:00
-- url     : https://prove2.me/theorems/17e36f6e-b0c4-4726-b000-2b5f44570dcb
-- title:
--   The Lean 4 theorem `galerkinSpan_mono` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinSpan_mono` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.galerkinSpan_mono
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.galerkinSpan_mono (b : HilbertBasis ℕ ℂ F) {m n : ℕ} (hmn : m ≤ n) :
    galerkinSpan b m ≤ galerkinSpan b n := by sorry

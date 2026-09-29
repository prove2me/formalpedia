-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_basis_mem_galerkinSpan
-- name    : BookProof.HermiteGalerkin.basis_mem_galerkinSpan
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:34:39.698081+00:00
-- url     : https://prove2.me/theorems/63c42df5-09ed-49b0-86fa-0a3376204f6b
-- title:
--   The Lean 4 theorem `basis_mem_galerkinSpan` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `basis_mem_galerkinSpan` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.basis_mem_galerkinSpan
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.basis_mem_galerkinSpan (b : HilbertBasis ℕ ℂ F) {i m : ℕ} (him : i < m) :
    b i ∈ galerkinSpan b m := by sorry

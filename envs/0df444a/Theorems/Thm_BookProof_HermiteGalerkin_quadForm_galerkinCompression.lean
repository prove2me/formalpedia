-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_quadForm_galerkinCompression
-- name    : BookProof.HermiteGalerkin.quadForm_galerkinCompression
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:16:56.305012+00:00
-- url     : https://prove2.me/theorems/26e9968d-3f44-492d-8d84-eb011023946d
-- title:
--   The Lean 4 theorem `quadForm_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadForm_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.quadForm_galerkinCompression
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.quadForm_galerkinCompression (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    {u : F} (hu : u ∈ galerkinSpan b m) :
    (inner ℂ u (galerkinCompression A b m u) : ℂ).re = (inner ℂ u (A u) : ℂ).re := by sorry

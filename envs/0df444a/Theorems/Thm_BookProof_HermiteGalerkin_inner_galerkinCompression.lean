-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_inner_galerkinCompression
-- name    : BookProof.HermiteGalerkin.inner_galerkinCompression
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:09.739632+00:00
-- url     : https://prove2.me/theorems/71956415-481b-49f7-9a05-ff3859b95b26
-- title:
--   The Lean 4 theorem `inner_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_galerkinCompression` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.inner_galerkinCompression
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.inner_galerkinCompression (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    {u : F} (hu : u ∈ galerkinSpan b m) :
    (inner ℂ u (galerkinCompression A b m u) : ℂ) = inner ℂ u (A u) := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteGalerkin_galerkinCompression_apply
-- name    : BookProof.HermiteGalerkin.galerkinCompression_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:31:22.464425+00:00
-- url     : https://prove2.me/theorems/b0f392bd-9ab2-4632-9499-176a48882381
-- title:
--   The Lean 4 theorem `galerkinCompression_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `galerkinCompression_apply` in the `ChapterHermiteGalerkinFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteGalerkinFriedrichs.lean

-- Generated from ChapterHermiteGalerkinFriedrichs.lean — theorem BookProof.HermiteGalerkin.galerkinCompression_apply
import Mathlib
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
open BookProof.HermiteGalerkin












open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open Filter Topology



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.HermiteGalerkin.galerkinCompression_apply (A : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (m : ℕ)
    (u : F) : galerkinCompression A b m u
      = (galerkinSpan b m).starProjection (A ((galerkinSpan b m).starProjection u)) := by sorry

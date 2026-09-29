-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_annPoly_hermiteMvLp
-- name    : BookProof.HermiteProductBasis.annPoly_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:31.215135+00:00
-- url     : https://prove2.me/theorems/7f3e0f7f-3b9d-47e5-98f8-94f3f63c2d48
-- title:
--   The Lean 4 theorem `annPoly_hermiteMvLp` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `annPoly_hermiteMvLp` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.annPoly_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.annPoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (annPoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (a - Finsupp.single i 1) := by sorry

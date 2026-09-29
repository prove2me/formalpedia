-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMvLp
-- name    : BookProof.HermiteProductBasis.crePoly_hermiteMvLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:54:29.141992+00:00
-- url     : https://prove2.me/theorems/f53aa08c-017e-4189-a52d-6a765b0f8124
-- title:
--   The Lean 4 theorem `crePoly_hermiteMvLp` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crePoly_hermiteMvLp` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.crePoly_hermiteMvLp
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.crePoly_hermiteMvLp (i : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (crePoly i (hermiteMv a))
      = ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (a + Finsupp.single i 1) := by sorry

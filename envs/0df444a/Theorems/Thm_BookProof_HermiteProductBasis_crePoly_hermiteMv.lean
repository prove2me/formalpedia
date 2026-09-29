-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_crePoly_hermiteMv
-- name    : BookProof.HermiteProductBasis.crePoly_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:38.494686+00:00
-- url     : https://prove2.me/theorems/8232d6ae-0262-4542-9608-4b4408bda329
-- title:
--   The Lean 4 theorem `crePoly_hermiteMv` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crePoly_hermiteMv` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.crePoly_hermiteMv
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.crePoly_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    crePoly i (hermiteMv a) = hermiteMv (a + Finsupp.single i 1) := by sorry

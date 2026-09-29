-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteMv
-- name    : BookProof.HermiteProductBasis.pderiv_hermiteMv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:17:25.767226+00:00
-- url     : https://prove2.me/theorems/f30b6bd6-4bae-46fb-99d7-988f6f6b1fc1
-- title:
--   The Lean 4 theorem `pderiv_hermiteMv` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_hermiteMv` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pderiv_hermiteMv
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pderiv_hermiteMv (i : Fin d) (a : Fin d →₀ ℕ) :
    pderiv i (hermiteMv a) = ((a i : ℂ)) • hermiteMv (a - Finsupp.single i 1) := by sorry

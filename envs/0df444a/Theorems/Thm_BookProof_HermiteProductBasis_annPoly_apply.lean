-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_annPoly_apply
-- name    : BookProof.HermiteProductBasis.annPoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:44:09.63603+00:00
-- url     : https://prove2.me/theorems/e9fa88ef-3802-4350-9ead-d35ec952338a
-- title:
--   The Lean 4 theorem `annPoly_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `annPoly_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.annPoly_apply
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.annPoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    annPoly i p = pderiv i p := by sorry

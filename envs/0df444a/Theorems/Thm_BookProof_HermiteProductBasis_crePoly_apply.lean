-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_crePoly_apply
-- name    : BookProof.HermiteProductBasis.crePoly_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:44:22.490493+00:00
-- url     : https://prove2.me/theorems/54a92bf7-23e4-4eac-8d34-5e7b69fca2d0
-- title:
--   The Lean 4 theorem `crePoly_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `crePoly_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.crePoly_apply
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.crePoly_apply (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    crePoly i p = X i * p - pderiv i p := by sorry

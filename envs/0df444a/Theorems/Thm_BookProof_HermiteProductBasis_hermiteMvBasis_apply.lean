-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_hermiteMvBasis_apply
-- name    : BookProof.HermiteProductBasis.hermiteMvBasis_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:47:10.008789+00:00
-- url     : https://prove2.me/theorems/a4959304-21fc-4518-8921-a1daab4a9aae
-- title:
--   The Lean 4 theorem `hermiteMvBasis_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hermiteMvBasis_apply` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.hermiteMvBasis_apply
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.hermiteMvBasis_apply (a : Fin d →₀ ℕ) :
    hermiteMvBasis a = hermiteMvLp (d := d) a := by sorry

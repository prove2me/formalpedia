-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteFactor_self
-- name    : BookProof.HermiteProductBasis.pderiv_hermiteFactor_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:45.466727+00:00
-- url     : https://prove2.me/theorems/3ab77f0d-b080-4637-9661-72614054ef51
-- title:
--   The Lean 4 theorem `pderiv_hermiteFactor_self` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_hermiteFactor_self` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pderiv_hermiteFactor_self
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pderiv_hermiteFactor_self (i : Fin d) (n : ℕ) :
    pderiv i (hermiteFactor i n) = (n : ℂ) • hermiteFactor i (n - 1) := by sorry

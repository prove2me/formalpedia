-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pderiv_hermiteFactor_other
-- name    : BookProof.HermiteProductBasis.pderiv_hermiteFactor_other
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:09:22.805446+00:00
-- url     : https://prove2.me/theorems/acc1f4bb-6107-4175-91f3-71973aa054e5
-- title:
--   The Lean 4 theorem `pderiv_hermiteFactor_other` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_hermiteFactor_other` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pderiv_hermiteFactor_other
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pderiv_hermiteFactor_other {i j : Fin d} (h : j ≠ i) (n : ℕ) :
    pderiv j (hermiteFactor i n) = 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pderiv_aeval_other
-- name    : BookProof.HermiteProductBasis.pderiv_aeval_other
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:18.829563+00:00
-- url     : https://prove2.me/theorems/b1daa5bb-cc8f-434a-8c3d-3e06feeebc5e
-- title:
--   The Lean 4 theorem `pderiv_aeval_other` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_aeval_other` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pderiv_aeval_other
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pderiv_aeval_other {i j : Fin d} (h : j ≠ i) (q : Polynomial ℂ) :
    pderiv j (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q) = 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteProductBasis_pderiv_aeval_self
-- name    : BookProof.HermiteProductBasis.pderiv_aeval_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:18.046358+00:00
-- url     : https://prove2.me/theorems/94371fb2-62ce-4099-a8c7-94f0b6e81971
-- title:
--   The Lean 4 theorem `pderiv_aeval_self` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pderiv_aeval_self` in the `ChapterHermiteProductBasis` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteProductBasis.lean

-- Generated from ChapterHermiteProductBasis.lean — theorem BookProof.HermiteProductBasis.pderiv_aeval_self
import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.HermiteProductBasis







open MeasureTheory MvPolynomial BookProof.HermiteCore BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

theorem BookProof.HermiteProductBasis.pderiv_aeval_self (i : Fin d) (q : Polynomial ℂ) :
    pderiv i (Polynomial.aeval (X i : MvPolynomial (Fin d) ℂ) q)
      = Polynomial.aeval (X i) (Polynomial.derivative q) := by sorry

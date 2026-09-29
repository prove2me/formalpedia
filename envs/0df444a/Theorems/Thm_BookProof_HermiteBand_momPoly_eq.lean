-- Prove2me | Theorems.Thm_BookProof_HermiteBand_momPoly_eq
-- name    : BookProof.HermiteBand.momPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:01:07.331388+00:00
-- url     : https://prove2.me/theorems/c71ddc17-dd13-47d6-bd99-ad5985a329c5
-- title:
--   The Lean 4 theorem `momPoly_eq` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momPoly_eq` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.momPoly_eq
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.momPoly_eq (i : Fin d) :
    (momPoly i : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
      = (Complex.I / 2) • crePoly i + (-(Complex.I / 2)) • annPoly i := by sorry

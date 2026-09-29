-- Prove2me | Theorems.Thm_BookProof_HermiteBand_mulXPoly_eq
-- name    : BookProof.HermiteBand.mulXPoly_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T12:01:19.673898+00:00
-- url     : https://prove2.me/theorems/bd60b576-defc-4c01-88a9-65ee60c89ab2
-- title:
--   The Lean 4 theorem `mulXPoly_eq` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulXPoly_eq` in the `ChapterHermiteBandCalculus` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculus.lean

-- Generated from ChapterHermiteBandCalculus.lean — theorem BookProof.HermiteBand.mulXPoly_eq
import Mathlib
import Definitions.Def_ChapterHermiteBandCalculus
open BookProof.HermiteBand







noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis

variable {d : ℕ}

























open BookProof.NavierStokesFlow.DifferentialL2 BookProof.FullQuadratic

theorem BookProof.HermiteBand.mulXPoly_eq (i : Fin d) :
    (mulXPoly i : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
      = crePoly i + annPoly i := by sorry

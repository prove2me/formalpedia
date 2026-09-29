-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_mulXPoly_eq_mulOp
-- name    : BookProof.HermiteRelative.mulXPoly_eq_mulOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:50:19.263576+00:00
-- url     : https://prove2.me/theorems/66eb7a7e-50fe-4835-b240-a35d24e16b93
-- title:
--   The Lean 4 theorem `mulXPoly_eq_mulOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `mulXPoly_eq_mulOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.mulXPoly_eq_mulOp
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

theorem BookProof.HermiteRelative.mulXPoly_eq_mulOp (i : Fin d) :
    mulXPoly i = BookProof.YangMillsHermite.mulOp (X i : MvPolynomial (Fin d) ℂ) := by sorry

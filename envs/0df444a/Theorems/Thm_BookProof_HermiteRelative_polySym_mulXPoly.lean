-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_polySym_mulXPoly
-- name    : BookProof.HermiteRelative.polySym_mulXPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:29.825907+00:00
-- url     : https://prove2.me/theorems/4c81c7e4-d07d-4115-b95b-b5f9f9288610
-- title:
--   The Lean 4 theorem `polySym_mulXPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polySym_mulXPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.polySym_mulXPoly
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

theorem BookProof.HermiteRelative.polySym_mulXPoly (i : Fin d) : BookProof.YangMillsHermite.PolySym (mulXPoly i) := by sorry

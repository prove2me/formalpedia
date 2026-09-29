-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_polySym_momPoly
-- name    : BookProof.HermiteRelative.polySym_momPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:26.923984+00:00
-- url     : https://prove2.me/theorems/ff7cbe17-15fc-4017-afea-3b690982e94a
-- title:
--   The Lean 4 theorem `polySym_momPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `polySym_momPoly` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.polySym_momPoly
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

theorem BookProof.HermiteRelative.polySym_momPoly (i : Fin d) : BookProof.YangMillsHermite.PolySym (momPoly i) := by sorry

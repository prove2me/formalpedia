-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_posL_symmetric
-- name    : BookProof.HermiteRelative.posL_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:18:05.301053+00:00
-- url     : https://prove2.me/theorems/9c46cee4-dd97-4856-ac92-42581d6287c4
-- title:
--   The Lean 4 theorem `posL_symmetric` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `posL_symmetric` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.posL_symmetric
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

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive

theorem BookProof.HermiteRelative.posL_symmetric (i : Fin d) : SymmetricOn (polyGaussCore (d := d)) (posL i) := by sorry

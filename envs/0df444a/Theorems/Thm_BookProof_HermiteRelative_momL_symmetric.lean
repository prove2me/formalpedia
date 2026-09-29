-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_momL_symmetric
-- name    : BookProof.HermiteRelative.momL_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:18:03.574188+00:00
-- url     : https://prove2.me/theorems/3273e21f-ea57-4b34-8cc4-38ad850fe98a
-- title:
--   The Lean 4 theorem `momL_symmetric` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momL_symmetric` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.momL_symmetric
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

theorem BookProof.HermiteRelative.momL_symmetric (i : Fin d) : SymmetricOn (polyGaussCore (d := d)) (momL i) := by sorry

-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_foOp_apply
-- name    : BookProof.HermiteRelative.foOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:17:41.054516+00:00
-- url     : https://prove2.me/theorems/1bef9c2c-7821-4cd1-8255-c665b4e13ae2
-- title:
--   The Lean 4 theorem `foOp_apply` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `foOp_apply` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.foOp_apply
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

theorem BookProof.HermiteRelative.foOp_apply (b b' : Fin d → ℝ) (u : polyGaussCore (d := d)) :
    foOp b b' u = ∑ i, (((b i : ℝ) : ℂ) • posL i u + ((b' i : ℝ) : ℂ) • momL i u) := by sorry

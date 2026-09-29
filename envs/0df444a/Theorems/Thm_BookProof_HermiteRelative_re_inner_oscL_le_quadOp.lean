-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_re_inner_oscL_le_quadOp
-- name    : BookProof.HermiteRelative.re_inner_oscL_le_quadOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:40.447388+00:00
-- url     : https://prove2.me/theorems/00458fde-1ee2-41cb-86a2-b4145b668ba6
-- title:
--   The Lean 4 theorem `re_inner_oscL_le_quadOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_inner_oscL_le_quadOp` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.re_inner_oscL_le_quadOp
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

theorem BookProof.HermiteRelative.re_inner_oscL_le_quadOp (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (i : Fin d) (u : polyGaussCore (d := d)) :
    c0 * (inner ℂ (u : L2d d) (oscL i u) : ℂ).re
      ≤ (inner ℂ (u : L2d d) (quadOp c u) : ℂ).re := by sorry

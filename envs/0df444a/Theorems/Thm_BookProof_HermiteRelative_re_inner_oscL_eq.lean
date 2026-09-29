-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_re_inner_oscL_eq
-- name    : BookProof.HermiteRelative.re_inner_oscL_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:22.33108+00:00
-- url     : https://prove2.me/theorems/1cffbb90-4b71-4c31-ad60-0f0a92a9d396
-- title:
--   The Lean 4 theorem `re_inner_oscL_eq` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_inner_oscL_eq` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.re_inner_oscL_eq
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

theorem BookProof.HermiteRelative.re_inner_oscL_eq (i : Fin d) (u : polyGaussCore (d := d)) :
    (inner ℂ (u : L2d d) (oscL i u) : ℂ).re
      = ‖momL i u‖ ^ 2 + ‖posL i u‖ ^ 2 / 4 := by sorry

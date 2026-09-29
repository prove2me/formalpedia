-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_norm_posL_le
-- name    : BookProof.HermiteRelative.norm_posL_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:38.917677+00:00
-- url     : https://prove2.me/theorems/5d184276-1238-42be-a113-1922bd07b6a3
-- title:
--   The Lean 4 theorem `norm_posL_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_posL_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.norm_posL_le
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

theorem BookProof.HermiteRelative.norm_posL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖posL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ := by sorry

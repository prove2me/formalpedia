-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_norm_momL_le
-- name    : BookProof.HermiteRelative.norm_momL_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:25.490687+00:00
-- url     : https://prove2.me/theorems/c1fea039-179b-4332-92c8-c8146f47be6e
-- title:
--   The Lean 4 theorem `norm_momL_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_momL_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.norm_momL_le
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

theorem BookProof.HermiteRelative.norm_momL_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    {e : ℝ} (he : 0 < e) (i : Fin d) (u : polyGaussCore (d := d)) :
    ‖momL i u‖ ≤ e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖ := by sorry

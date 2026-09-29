-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_norm_foOp_le
-- name    : BookProof.HermiteRelative.norm_foOp_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:19:34.123699+00:00
-- url     : https://prove2.me/theorems/1d0d5508-7dd5-442d-8121-418bf73e86c8
-- title:
--   The Lean 4 theorem `norm_foOp_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_foOp_le` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.norm_foOp_le
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

theorem BookProof.HermiteRelative.norm_foOp_le (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0) (hc : ∀ i, c0 ≤ c i)
    (b b' : Fin d → ℝ) {e : ℝ} (he : 0 < e) (u : polyGaussCore (d := d)) :
    ‖foOp b b' u‖
      ≤ (∑ i, (|b i| + |b' i|)) * (e * ‖quadOp c u‖ + (2 / (c0 * e)) * ‖(u : L2d d)‖) := by sorry

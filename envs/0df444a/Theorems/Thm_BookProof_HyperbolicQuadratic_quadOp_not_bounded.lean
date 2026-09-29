-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_not_bounded
-- name    : BookProof.HyperbolicQuadratic.quadOp_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:43.287227+00:00
-- url     : https://prove2.me/theorems/d051bcd6-b352-4717-bce2-d0f6ca76b37c
-- title:
--   The Lean 4 theorem `quadOp_not_bounded` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_not_bounded` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_not_bounded
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

theorem BookProof.HyperbolicQuadratic.quadOp_not_bounded (c : Fin d → ℝ) {i : Fin d} (hci : c i ≠ 0) :
    ¬ ∃ C : ℝ, ∀ f : polyGaussCore (d := d), ‖quadOp c f‖ ≤ C * ‖(f : L2d d)‖ := by sorry

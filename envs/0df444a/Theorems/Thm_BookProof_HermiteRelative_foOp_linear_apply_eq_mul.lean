-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_foOp_linear_apply_eq_mul
-- name    : BookProof.HermiteRelative.foOp_linear_apply_eq_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:48:52.688416+00:00
-- url     : https://prove2.me/theorems/9725ca1b-9279-46a9-8f32-f65725f51c3d
-- title:
--   The Lean 4 theorem `foOp_linear_apply_eq_mul` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `foOp_linear_apply_eq_mul` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.foOp_linear_apply_eq_mul
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

theorem BookProof.HermiteRelative.foOp_linear_apply_eq_mul (b : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (foPoly b 0 p) x = ((∑ i, b i * x i : ℝ) : ℂ) * pgFun p x := by sorry

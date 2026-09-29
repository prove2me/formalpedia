-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_quadOp_add_firstOrder_essentiallySelfAdjoint
-- name    : BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T00:20:18.867518+00:00
-- url     : https://prove2.me/theorems/42767449-3974-4205-82c6-b071e34edb62
-- title:
--   The Lean 4 theorem `quadOp_add_firstOrder_essentiallySelfAdjoint` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_add_firstOrder_essentiallySelfAdjoint` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint
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

theorem BookProof.HermiteRelative.quadOp_add_firstOrder_essentiallySelfAdjoint (c : Fin d → ℝ) {c0 : ℝ} (hc0 : 0 < c0)
    (hc : ∀ i, c0 ≤ c i) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (quadOp c + foOp b b') := by sorry

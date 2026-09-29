-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_add_boundedPotential_essentiallySelfAdjoint
-- name    : BookProof.HyperbolicQuadratic.quadOp_add_boundedPotential_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:07:02.692033+00:00
-- url     : https://prove2.me/theorems/3b0a2c34-3250-4878-96c5-efd141002dd1
-- title:
--   The Lean 4 theorem `quadOp_add_boundedPotential_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_add_boundedPotential_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_add_boundedPotential_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHyperbolicQuadraticEsa
open BookProof.HyperbolicQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

open scoped ENNReal in

theorem BookProof.HyperbolicQuadratic.quadOp_add_boundedPotential_essentiallySelfAdjoint (c : Fin d → ℝ)
    (W : MeasureTheory.Lp ℂ (⊤ : ℝ≥0∞) (volume : Measure (Vd d)))
    (hW : ∀ᵐ x ∂(volume : Measure (Vd d)), (starRingEnd ℂ) (W x) = W x) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp c + ((BookProof.StrichartzWave.mulL2 W).toLinearMap ∘ₗ
        (polyGaussCore (d := d)).subtype)) := by sorry

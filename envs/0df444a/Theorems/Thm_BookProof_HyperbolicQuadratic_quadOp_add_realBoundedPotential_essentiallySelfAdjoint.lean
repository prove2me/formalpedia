-- Prove2me | Theorems.Thm_BookProof_HyperbolicQuadratic_quadOp_add_realBoundedPotential_essentiallySelfAdjoint
-- name    : BookProof.HyperbolicQuadratic.quadOp_add_realBoundedPotential_essentiallySelfAdjoint
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T07:06:58.174265+00:00
-- url     : https://prove2.me/theorems/1252b9aa-e28e-482a-9551-9b5047d610c6
-- title:
--   The Lean 4 theorem `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` in the `ChapterHyperbolicQuadraticEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

-- Generated from ChapterHyperbolicQuadraticEsa.lean — theorem BookProof.HyperbolicQuadratic.quadOp_add_realBoundedPotential_essentiallySelfAdjoint
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

theorem BookProof.HyperbolicQuadratic.quadOp_add_realBoundedPotential_essentiallySelfAdjoint (c : Fin d → ℝ)
    (W : Vd d → ℝ)
    (hW : MeasureTheory.MemLp (fun x => (W x : ℂ)) (⊤ : ℝ≥0∞) (volume : Measure (Vd d))) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d))
      (quadOp c + ((BookProof.StrichartzWave.mulL2 (hW.toLp _)).toLinearMap ∘ₗ
        (polyGaussCore (d := d)).subtype)) := by sorry

-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadPolyMat_apply
-- name    : BookProof.QuadraticRotation.quadPolyMat_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T23:23:30.255698+00:00
-- url     : https://prove2.me/theorems/26edb4b2-7bdc-4a1f-9115-c47917edf216
-- title:
--   The Lean 4 theorem `quadPolyMat_apply` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.quadPolyMat_apply` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadPolyMat_apply
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadPolyMat_apply (A : Matrix (Fin d) (Fin d) ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPolyMat A p = ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
      (momPoly k (momPoly l p) + (1/4 : ℂ) • (X k * (X l * p))) := by sorry

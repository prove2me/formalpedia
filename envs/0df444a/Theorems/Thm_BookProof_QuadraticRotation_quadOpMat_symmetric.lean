-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_symmetric
-- name    : BookProof.QuadraticRotation.quadOpMat_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T04:58:11.033972+00:00
-- url     : https://prove2.me/theorems/8442e69f-c116-41c2-a34e-453a44156e29
-- title:
--   The Lean 4 theorem `quadOpMat_symmetric` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   Formal statement of `BookProof.QuadraticRotation.quadOpMat_symmetric` from the timepiece Lean 4 formalization.
-- source:
--   https://github.com/leonardopedro/timepiece

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadOpMat_symmetric
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadOpMat_symmetric {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) :
    SymmetricOn (polyGaussCore (d := d)) (quadOpMat A) := by sorry

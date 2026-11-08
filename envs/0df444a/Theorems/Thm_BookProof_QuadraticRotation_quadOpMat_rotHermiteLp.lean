-- Prove2me | Theorems.Thm_BookProof_QuadraticRotation_quadOpMat_rotHermiteLp
-- name    : BookProof.QuadraticRotation.quadOpMat_rotHermiteLp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T00:25:09.114744+00:00
-- url     : https://prove2.me/theorems/1ed138c2-7847-440c-9a26-edeb6a7715ea
-- title:
--   The Lean 4 theorem `quadOpMat_rotHermiteLp` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadOpMat_rotHermiteLp` in the `ChapterQuadraticRotationEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQuadraticRotationEsa.lean

-- Generated from ChapterQuadraticRotationEsa.lean — theorem BookProof.QuadraticRotation.quadOpMat_rotHermiteLp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QuadraticRotation



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

theorem BookProof.QuadraticRotation.quadOpMat_rotHermiteLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a : Fin d →₀ ℕ) (h : rotHermiteLp O a ∈ polyGaussCore (d := d)) :
    quadOpMat (rotConj O c) ⟨rotHermiteLp O a, h⟩
      = ((quadSymbol c a : ℝ) : ℂ) • rotHermiteLp O a := by sorry

-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_quadPolyMatT_apply_expand
-- name    : BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:45:17.211842+00:00
-- url     : https://prove2.me/theorems/3d5e4edb-7e58-4b64-befa-ea912c3603a5
-- title:
--   `BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand` (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (f : MvPolynomial (Fin d) ℂ) : quadPolyMatT a k A f = quadPolyMat A f + ∑ p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand` (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ) (f : MvPolynomial (Fin d) ℂ) : quadPolyMatT a k A f = quadPolyMat A f + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f) + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f) + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadraticMatrix



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticMatrix.quadPolyMatT_apply_expand (a k : Vd d) (A : Matrix (Fin d) (Fin d) ℝ)
    (f : MvPolynomial (Fin d) ℂ) :
    quadPolyMatT a k A f
      = quadPolyMat A f
        + ∑ p, ∑ q, ((A p q * k q : ℝ) : ℂ) • momPoly p f
        + ∑ p, ∑ q, ((A p q * k p : ℝ) : ℂ) • momPoly q f
        + ∑ p, ∑ q, ((A p q * a q / 4 : ℝ) : ℂ) • (X p * f)
        + ∑ p, ∑ q, ((A p q * a p / 4 : ℝ) : ℂ) • (X q * f)
        + ∑ p, ∑ q, ((A p q * (k p * k q + a p * a q / 4) : ℝ) : ℂ) • f := by sorry

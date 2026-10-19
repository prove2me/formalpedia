-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticMatrix_shiftedHMatOp_hermiteTRLp
-- name    : BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:47:03.226622+00:00
-- url     : https://prove2.me/theorems/3cd54ae9-cbc3-49ee-8473-e237c60d2ba2
-- title:
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym : ∀ i j, rotConj
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticMatrixEsa`.
--
--   `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym : ∀ i j, rotConj O c i j = rotConj O c j i) (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i) (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) : shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩ = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp`.

-- Generated from ChapterShiftedQuadraticMatrixEsa.lean — theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
open BookProof.HermiteProductBasis
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
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

theorem BookProof.ShiftedQuadraticMatrix.shiftedHMatOp_hermiteTRLp {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2)
    (α : Fin d →₀ ℕ) (h : hermiteTRLp O a k α ∈ polyGaussCoreT a k) :
    shiftedHMatOp a k (rotConj O c) b b' ⟨_, h⟩
      = (((quadSymbol c α + matShiftConst a k b b' : ℝ)) : ℂ) • hermiteTRLp O a k α := by sorry

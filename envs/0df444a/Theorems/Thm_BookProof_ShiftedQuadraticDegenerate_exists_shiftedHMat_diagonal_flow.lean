-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_shiftedHMat_diagonal_flow
-- name    : BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:25:38.688447+00:00
-- url     : https://prove2.me/theorems/e0377106-6061-4686-bf4d-a0477182a29a
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym : ∀ i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow` {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ) (hsym : ∀ i j, rotConj O c i j = rotConj O c j i) (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i) (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (shiftedHMatOp a k (rotConj O c) b b') T.op ∧ IsStoneFlow T U ∧ ∀ (α : Fin d →₀ ℕ) (t : ℝ), U t (hermiteTRLp O a k α) = Complex.exp (-(Complex.I * ((quadSymbol c α + matShiftConst a k b b' : ℝ) : ℂ) * t)) • hermiteTRLp O a k α
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQuadraticRotationEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterShiftedQuadraticMatrixEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneEigenflow
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticDegenerate
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.StoneBridge
open BookProof.ShiftedQuadraticDegenerate



open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HyperbolicQuadratic
open BookProof.QuadraticRotation
open BookProof.ShiftedHermiteCore
open BookProof.ShiftedQuadratic
open BookProof.ShiftedQuadraticMatrix
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.StoneEigenflow

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedHMat_diagonal_flow {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (a k : Vd d) (b b' : Fin d → ℝ)
    (hsym : ∀ i j, rotConj O c i j = rotConj O c j i)
    (ha : ∀ i, ∑ j, rotConj O c i j * a j = -2 * b i)
    (hk : ∀ i, ∑ j, rotConj O c i j * k j = -(b' i) / 2) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (shiftedHMatOp a k (rotConj O c) b b') T.op ∧
      IsStoneFlow T U ∧
      ∀ (α : Fin d →₀ ℕ) (t : ℝ),
        U t (hermiteTRLp O a k α)
          = Complex.exp (-(Complex.I * ((quadSymbol c α + matShiftConst a k b b' : ℝ) : ℂ) * t))
              • hermiteTRLp O a k α := by sorry

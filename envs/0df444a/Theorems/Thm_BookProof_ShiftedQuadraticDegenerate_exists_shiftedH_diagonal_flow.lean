-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadraticDegenerate_exists_shiftedH_diagonal_flow
-- name    : BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:13.930848+00:00
-- url     : https://prove2.me/theorems/9129e4d6-65dc-48fe-bcd8-d24b52b7db93
-- title:
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticDegenerate`.
--
--   `BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧ IsStoneFlow T U ∧ ∀ (α : Fin d →₀ ℕ) (t : ℝ), U t (hermiteTLp (shiftVec c b) (boostVec c b') α) = Complex.exp (-(Complex.I * ((quadSymbol c α + shiftConst c b b' : ℝ) : ℂ) * t)) • hermiteTLp (shiftVec c b) (boostVec c b') α
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow`.

-- Generated from ChapterShiftedQuadraticDegenerate.lean — theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow
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

theorem BookProof.ShiftedQuadraticDegenerate.exists_shiftedH_diagonal_flow (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension
        (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧
      IsStoneFlow T U ∧
      ∀ (α : Fin d →₀ ℕ) (t : ℝ),
        U t (hermiteTLp (shiftVec c b) (boostVec c b') α)
          = Complex.exp (-(Complex.I * ((quadSymbol c α + shiftConst c b b' : ℝ) : ℂ) * t))
              • hermiteTLp (shiftVec c b) (boostVec c b') α := by sorry

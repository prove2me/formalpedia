-- Prove2me | Theorems.Thm_BookProof_ShiftedQuadratic_shiftedHOp_stone_flow
-- name    : BookProof.ShiftedQuadratic.shiftedHOp_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T12:27:17.114048+00:00
-- url     : https://prove2.me/theorems/efdfe734-6f3d-4cfe-8e95-312d38ea2f1e
-- title:
--   `BookProof.ShiftedQuadratic.shiftedHOp_stone_flow` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExten
-- statement:
--   Prove the following Lean 4 theorem from `ChapterShiftedQuadraticEsa`.
--
--   `BookProof.ShiftedQuadratic.shiftedHOp_stone_flow` (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) : ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)), IsSelfAdjointExtension (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.ShiftedQuadratic.shiftedHOp_stone_flow`.

-- Generated from ChapterShiftedQuadraticEsa.lean — theorem BookProof.ShiftedQuadratic.shiftedHOp_stone_flow
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.EsaClosure
open BookProof.HermiteProductCore
open BookProof.ShiftedHermiteCore
open BookProof.StoneBridge
open BookProof.ShiftedQuadratic



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem BookProof.ShiftedQuadratic.shiftedHOp_stone_flow (c b b' : Fin d → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (shiftedHOp (shiftVec c b) (boostVec c b') c b b') T.op ∧
        IsStoneFlow T U := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_osc_stone_flow
-- name    : BookProof.FockWeightedSchur.osc_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:34:08.640986+00:00
-- url     : https://prove2.me/theorems/17fe1683-e8ea-4ba1-bbff-ebb7a6ad9eca
-- title:
--   `BookProof.FockWeightedSchur.osc_stone_flow` : ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)), IsSelfAdjointExtension (dGammaOp oscCol) T.op ∧ IsStoneFlow T U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.osc_stone_flow` : ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)), IsSelfAdjointExtension (dGammaOp oscCol) T.op ∧ IsStoneFlow T U
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.osc_stone_flow`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.osc_stone_flow
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterShiftedQuadraticEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.EsaClosure
open BookProof.FockSecondQuantization
open BookProof.StoneBridge
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.osc_stone_flow :
    ∃ (T : UnboundedSelfAdjoint Fock) (U : ℝ → (Fock →L[ℂ] Fock)),
      IsSelfAdjointExtension (dGammaOp oscCol) T.op ∧ IsStoneFlow T U := by sorry

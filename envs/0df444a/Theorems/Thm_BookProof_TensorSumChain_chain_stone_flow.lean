-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_chain_stone_flow
-- name    : BookProof.TensorSumChain.chain_stone_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:21.919811+00:00
-- url     : https://prove2.me/theorems/f4e3a596-74cc-418d-b21e-ad7ea92d6f10
-- title:
--   `BookProof.TensorSumChain.chain_stone_flow` (E : EsaOp) (L : List EsaOp) : ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier) (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.chain_stone_flow` (E : EsaOp) (L : List EsaOp) : ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier) (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E L).space.carrier)), IsSelfAdjointExtension (chain E L).op G.op ∧ IsStoneFlow G U
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.chain_stone_flow`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.chain_stone_flow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.EsaClosure
open BookProof.StoneBridge



open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore
open BookProof.ChapterStoneResolvent

noncomputable section

theorem BookProof.TensorSumChain.chain_stone_flow (E : EsaOp) (L : List EsaOp) :
    ∃ (G : UnboundedSelfAdjoint (chain E L).space.carrier)
      (U : ℝ → ((chain E L).space.carrier →L[ℂ] (chain E L).space.carrier)),
      IsSelfAdjointExtension (chain E L).op G.op ∧ IsStoneFlow G U := by sorry

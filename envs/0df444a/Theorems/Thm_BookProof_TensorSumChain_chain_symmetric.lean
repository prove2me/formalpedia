-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_chain_symmetric
-- name    : BookProof.TensorSumChain.chain_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T15:10:05.549203+00:00
-- url     : https://prove2.me/theorems/8e0b3a9c-91f9-40da-bdb7-4b3bac171427
-- title:
--   `BookProof.TensorSumChain.chain_symmetric` (E : EsaOp) (L : List EsaOp) : SymmetricOn (chain E L).dom (chain E L).op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.chain_symmetric` (E : EsaOp) (L : List EsaOp) : SymmetricOn (chain E L).dom (chain E L).op
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.chain_symmetric`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.chain_symmetric
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterPermutationSectorEsa



open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore

noncomputable section

theorem BookProof.TensorSumChain.chain_symmetric (E : EsaOp) (L : List EsaOp) :
    SymmetricOn (chain E L).dom (chain E L).op := by sorry

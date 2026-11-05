-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_chain_esa
-- name    : BookProof.TensorSumChain.chain_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T15:11:19.611034+00:00
-- url     : https://prove2.me/theorems/c4b81aa2-bcb2-4dc0-b102-ae7b88dc5cda
-- title:
--   `BookProof.TensorSumChain.chain_esa` (E : EsaOp) (L : List EsaOp) : EssentiallySelfAdjointOn (chain E L).dom (chain E L).op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.chain_esa` (E : EsaOp) (L : List EsaOp) : EssentiallySelfAdjointOn (chain E L).dom (chain E L).op
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.chain_esa`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.chain_esa
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

theorem BookProof.TensorSumChain.chain_esa (E : EsaOp) (L : List EsaOp) :
    EssentiallySelfAdjointOn (chain E L).dom (chain E L).op := by sorry

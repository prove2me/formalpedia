-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_chain_dense
-- name    : BookProof.TensorSumChain.chain_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T15:12:22.76458+00:00
-- url     : https://prove2.me/theorems/d0401b79-e5fb-4aaf-8b28-8ef33297b322
-- title:
--   `BookProof.TensorSumChain.chain_dense` (E : EsaOp) (L : List EsaOp) : Dense (((chain E L).dom : Submodule ℂ (chain E L).space.carrier) : Set (chain E L).space.carrier)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.chain_dense` (E : EsaOp) (L : List EsaOp) : Dense (((chain E L).dom : Submodule ℂ (chain E L).space.carrier) : Set (chain E L).space.carrier)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.chain_dense`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.chain_dense
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterPermutationSectorEsa



open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore

noncomputable section

theorem BookProof.TensorSumChain.chain_dense (E : EsaOp) (L : List EsaOp) :
    Dense (((chain E L).dom : Submodule ℂ (chain E L).space.carrier) :
      Set (chain E L).space.carrier) := by sorry

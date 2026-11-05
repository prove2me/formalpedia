-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_positionChain_esa
-- name    : BookProof.TensorSumChain.positionChain_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T15:11:20.403087+00:00
-- url     : https://prove2.me/theorems/ad88a190-dce7-4394-bb6e-c4111ba26f53
-- title:
--   `BookProof.TensorSumChain.positionChain_esa` (n : ℕ) : EssentiallySelfAdjointOn (chain posEsaOp (List.replicate n posEsaOp)).dom (chain posEsaOp (List.replicate n posEsaOp)).op
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.positionChain_esa` (n : ℕ) : EssentiallySelfAdjointOn (chain posEsaOp (List.replicate n posEsaOp)).dom (chain posEsaOp (List.replicate n posEsaOp)).op
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.positionChain_esa`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.positionChain_esa
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

theorem BookProof.TensorSumChain.positionChain_esa (n : ℕ) :
    EssentiallySelfAdjointOn (chain posEsaOp (List.replicate n posEsaOp)).dom
      (chain posEsaOp (List.replicate n posEsaOp)).op := by sorry

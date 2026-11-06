-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_pair_op_tmul
-- name    : BookProof.TensorSumChain.pair_op_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:58:11.743211+00:00
-- url     : https://prove2.me/theorems/45eab602-6682-4d0a-a841-e83c9fc5d0b4
-- title:
--   `BookProof.TensorSumChain.pair_op_tmul` (E F : EsaOp) (x : E.dom) (y : F.dom) (v : (pair E F).dom) (hv : (v : (pair E F).space.carrier) = pairEmb E.space F.space (inclPair E.space
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.pair_op_tmul` (E F : EsaOp) (x : E.dom) (y : F.dom) (v : (pair E F).dom) (hv : (v : (pair E F).space.carrier) = pairEmb E.space F.space (inclPair E.space F.space E.dom F.dom (x ⊗ₜ[ℂ] y))) : (pair E F).op v = pairEmb E.space F.space ((E.op x) ⊗ₜ[ℂ] (y : F.space.carrier) + (x : E.space.carrier) ⊗ₜ[ℂ] (F.op y))
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.pair_op_tmul`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.pair_op_tmul
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterPermutationSectorEsa



open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore
open BookProof.TensorSumEsa

noncomputable section

theorem BookProof.TensorSumChain.pair_op_tmul (E F : EsaOp) (x : E.dom) (y : F.dom)
    (v : (pair E F).dom)
    (hv : (v : (pair E F).space.carrier)
      = pairEmb E.space F.space (inclPair E.space F.space E.dom F.dom (x ⊗ₜ[ℂ] y))) :
    (pair E F).op v
      = pairEmb E.space F.space
        ((E.op x) ⊗ₜ[ℂ] (y : F.space.carrier) + (x : E.space.carrier) ⊗ₜ[ℂ] (F.op y)) := by sorry

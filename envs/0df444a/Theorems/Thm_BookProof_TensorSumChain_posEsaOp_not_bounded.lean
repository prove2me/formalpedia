-- Prove2me | Theorems.Thm_BookProof_TensorSumChain_posEsaOp_not_bounded
-- name    : BookProof.TensorSumChain.posEsaOp_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T15:11:54.039691+00:00
-- url     : https://prove2.me/theorems/ffc83c3b-08fd-4145-b2c5-7d18ae6cd1c8
-- title:
--   `BookProof.TensorSumChain.posEsaOp_not_bounded` : ¬ ∃ C : ℝ, ∀ x : posEsaOp.dom, ‖posEsaOp.op x‖ ≤ C * ‖(x : posEsaOp.space.carrier)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorSumChain`.
--
--   `BookProof.TensorSumChain.posEsaOp_not_bounded` : ¬ ∃ C : ℝ, ∀ x : posEsaOp.dom, ‖posEsaOp.op x‖ ≤ C * ‖(x : posEsaOp.space.carrier)‖
--
--   Formalization note: Lean 4 identifier `BookProof.TensorSumChain.posEsaOp_not_bounded`.

-- Generated from ChapterTensorSumChain.lean — theorem BookProof.TensorSumChain.posEsaOp_not_bounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterTensorSumEsa
import Mathlib
import Definitions.Def_ChapterTensorSumChain
import Definitions.Def_ChapterPermutationSectorEsa



open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore

noncomputable section

theorem BookProof.TensorSumChain.posEsaOp_not_bounded :
    ¬ ∃ C : ℝ, ∀ x : posEsaOp.dom,
      ‖posEsaOp.op x‖ ≤ C * ‖(x : posEsaOp.space.carrier)‖ := by sorry

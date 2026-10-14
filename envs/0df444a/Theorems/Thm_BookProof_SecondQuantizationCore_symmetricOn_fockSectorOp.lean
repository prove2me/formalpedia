-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_fockSectorOp
-- name    : BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:48:54.020277+00:00
-- url     : https://prove2.me/theorems/27706aba-61c6-42bb-a289-dd2cbdc31bed
-- title:
--   `BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp` (hA : SymmetricOn D₂ A) (n : ℕ) : SymmetricOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp` (hA : SymmetricOn D₂ A) (n : ℕ) : SymmetricOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.SecondQuantizationCore.symmetricOn_fockSectorOp (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n) := by sorry

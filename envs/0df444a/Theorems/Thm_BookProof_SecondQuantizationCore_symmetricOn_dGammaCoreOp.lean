-- Prove2me | Theorems.Thm_BookProof_SecondQuantizationCore_symmetricOn_dGammaCoreOp
-- name    : BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:49:33.919775+00:00
-- url     : https://prove2.me/theorems/0a76080f-a086-4cbe-a127-887a2c57f49a
-- title:
--   `BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp` (hA : SymmetricOn D₂ A) : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSecondQuantizationCoreEsa`.
--
--   `BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp` (hA : SymmetricOn D₂ A) : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D)
--
--   Formalization note: Lean 4 identifier `BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp`.

-- Generated from ChapterSecondQuantizationCoreEsa.lean — theorem BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.SecondQuantizationCore.symmetricOn_dGammaCoreOp (hA : SymmetricOn D₂ A) :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D) := by sorry

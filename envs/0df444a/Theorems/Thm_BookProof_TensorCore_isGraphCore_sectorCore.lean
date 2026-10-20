-- Prove2me | Theorems.Thm_BookProof_TensorCore_isGraphCore_sectorCore
-- name    : BookProof.TensorCore.isGraphCore_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:04:57.559984+00:00
-- url     : https://prove2.me/theorems/735b9406-9b07-4a0e-9350-5a5b20eb2ddd
-- title:
--   `BookProof.TensorCore.isGraphCore_sectorCore` (hcore : IsGraphCore D A) (n : ℕ) : IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.isGraphCore_sectorCore` (hcore : IsGraphCore D A) (n : ℕ) : IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.isGraphCore_sectorCore`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.isGraphCore_sectorCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGraphCoreTransfer
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.isGraphCore_sectorCore (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (sectorCore Hs D₂ D n) (sectorOp Hs D₂ A n) := by sorry

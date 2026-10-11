-- Prove2me | Theorems.Thm_BookProof_TensorCore_symmetricOn_sectorOp
-- name    : BookProof.TensorCore.symmetricOn_sectorOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:05:00.50801+00:00
-- url     : https://prove2.me/theorems/8913ed88-de79-4017-aa96-7207cc586cc2
-- title:
--   `BookProof.TensorCore.symmetricOn_sectorOp` (hA : SymmetricOn D₂ A) (n : ℕ) : SymmetricOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.symmetricOn_sectorOp` (hA : SymmetricOn D₂ A) (n : ℕ) : SymmetricOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.symmetricOn_sectorOp`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.symmetricOn_sectorOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.symmetricOn_sectorOp (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n) := by sorry

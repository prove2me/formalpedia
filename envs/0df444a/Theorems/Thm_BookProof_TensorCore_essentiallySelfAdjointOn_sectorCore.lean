-- Prove2me | Theorems.Thm_BookProof_TensorCore_essentiallySelfAdjointOn_sectorCore
-- name    : BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:13:40.126783+00:00
-- url     : https://prove2.me/theorems/a4d40fe2-3e83-4011-b88c-a6cefea2b209
-- title:
--   `BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore` (hcore : IsGraphCore D A) (n : ℕ) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : Essentiall
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore` (hcore : IsGraphCore D A) (n : ℕ) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) : EssentiallySelfAdjointOn (sectorCore Hs D₂ D n) (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n))
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.essentiallySelfAdjointOn_sectorCore (hcore : IsGraphCore D A) (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ n) (sectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (sectorCore Hs D₂ D n)
      (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)) := by sorry

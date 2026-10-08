-- Prove2me | Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
-- name    : BookProof.TensorCore.sectorCore_le_sectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:29.798138+00:00
-- url     : https://prove2.me/theorems/691bac82-d196-4cc6-a6f2-80e7f08e852e
-- title:
--   `BookProof.TensorCore.sectorCore_le_sectorDom` (n : ℕ) : sectorCore Hs D₂ D n ≤ sectorDom Hs D₂ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTensorGraphCore`.
--
--   `BookProof.TensorCore.sectorCore_le_sectorDom` (n : ℕ) : sectorCore Hs D₂ D n ≤ sectorDom Hs D₂ n
--
--   Formalization note: Lean 4 identifier `BookProof.TensorCore.sectorCore_le_sectorDom`.

-- Generated from ChapterTensorGraphCore.lean — theorem BookProof.TensorCore.sectorCore_le_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterDirectSumEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TensorCore.sectorCore_le_sectorDom (n : ℕ) :
    sectorCore Hs D₂ D n ≤ sectorDom Hs D₂ n := by sorry

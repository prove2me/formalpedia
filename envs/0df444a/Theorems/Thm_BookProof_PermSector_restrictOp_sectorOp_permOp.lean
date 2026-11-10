-- Prove2me | Theorems.Thm_BookProof_PermSector_restrictOp_sectorOp_permOp
-- name    : BookProof.PermSector.restrictOp_sectorOp_permOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-09T17:23:03.525947+00:00
-- url     : https://prove2.me/theorems/1ea0ca14-7a1f-4cc2-af59-5290527f49dd
-- title:
--   `BookProof.PermSector.restrictOp_sectorOp_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorCore Hs D₂ D n) : restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.restrictOp_sectorOp_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorCore Hs D₂ D n) : restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) ⟨permOp Hs n σ (x : (Hs.pow n).carrier), permOp_mem_sectorCore Hs D₂ D n σ x.2⟩ = permOp Hs n σ (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.restrictOp_sectorOp_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.restrictOp_sectorOp_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorCore
open BookProof.DirectSumEsa
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.restrictOp_sectorOp_permOp (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorCore Hs D₂ D n) :
    restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
        ⟨permOp Hs n σ (x : (Hs.pow n).carrier), permOp_mem_sectorCore Hs D₂ D n σ x.2⟩
      = permOp Hs n σ
          (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x) := by sorry

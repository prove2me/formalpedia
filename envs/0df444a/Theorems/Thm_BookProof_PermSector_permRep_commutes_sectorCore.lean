-- Prove2me | Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorCore
-- name    : BookProof.PermSector.permRep_commutes_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T20:17:05.610533+00:00
-- url     : https://prove2.me/theorems/14c502ee-7656-40a3-9a13-31472d25beb9
-- title:
--   `BookProof.PermSector.permRep_commutes_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorCore Hs D₂ D n) : restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permRep_commutes_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorCore Hs D₂ D n) : restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier), permRep_mem_sectorCore Hs D₂ D n σ _ x.2⟩ = (permRep Hs n).act σ (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permRep_commutes_sectorCore`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permRep_commutes_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterWignerOrbitClassification
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.permRep_commutes_sectorCore (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorCore Hs D₂ D n) :
    restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n)
        ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier),
          permRep_mem_sectorCore Hs D₂ D n σ _ x.2⟩
      = (permRep Hs n).act σ
          (restrictOp (sectorOp Hs D₂ A n) (sectorCore_le_sectorDom Hs D₂ D n) x) := by sorry

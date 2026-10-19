-- Prove2me | Theorems.Thm_BookProof_PermSector_permRep_commutes_sectorDom
-- name    : BookProof.PermSector.permRep_commutes_sectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:26.49669+00:00
-- url     : https://prove2.me/theorems/e661dc69-7144-45f3-970d-0b2b0321f51b
-- title:
--   `BookProof.PermSector.permRep_commutes_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier), perm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permRep_commutes_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier), permRep_mem_sectorDom Hs D₂ n σ _ x.2⟩ = (permRep Hs n).act σ (sectorOp Hs D₂ A n x)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permRep_commutes_sectorDom`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permRep_commutes_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Theorems.Thm_BookProof_PermSector_permRep_mem_sectorDom
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.permRep_commutes_sectorDom (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨(permRep Hs n).act σ (x : (Hs.pow n).carrier),
        permRep_mem_sectorDom Hs D₂ n σ _ x.2⟩
      = (permRep Hs n).act σ (sectorOp Hs D₂ A n x) := by sorry

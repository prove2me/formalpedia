-- Prove2me | Theorems.Thm_BookProof_PermSector_permRep_mem_sectorCore
-- name    : BookProof.PermSector.permRep_mem_sectorCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:10.491732+00:00
-- url     : https://prove2.me/theorems/c1cc128e-0ca1-4f5f-93da-bfa437f546d3
-- title:
--   `BookProof.PermSector.permRep_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorCore Hs D₂ D n) : (permRep Hs n).act σ x ∈ sectorCore Hs D₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permRep_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorCore Hs D₂ D n) : (permRep Hs n).act σ x ∈ sectorCore Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permRep_mem_sectorCore`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permRep_mem_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.permRep_mem_sectorCore (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier)
    (hx : x ∈ sectorCore Hs D₂ D n) : (permRep Hs n).act σ x ∈ sectorCore Hs D₂ D n := by sorry

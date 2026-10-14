-- Prove2me | Theorems.Thm_BookProof_PermSector_purePow_mem_sectorCore
-- name    : BookProof.PermSector.purePow_mem_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:09:30.599128+00:00
-- url     : https://prove2.me/theorems/1346bb69-dfe5-4424-bb40-d2ba06d66ee0
-- title:
--   `BookProof.PermSector.purePow_mem_sectorCore` (n : ℕ) (f : Fin n → Hs.carrier) (hD : D ≤ D₂) (hf : ∀ i, f i ∈ D) : purePow Hs n f ∈ sectorCore Hs D₂ D n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.purePow_mem_sectorCore` (n : ℕ) (f : Fin n → Hs.carrier) (hD : D ≤ D₂) (hf : ∀ i, f i ∈ D) : purePow Hs n f ∈ sectorCore Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.purePow_mem_sectorCore`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.purePow_mem_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.purePow_mem_sectorCore (n : ℕ) (f : Fin n → Hs.carrier) (hD : D ≤ D₂)
    (hf : ∀ i, f i ∈ D) : purePow Hs n f ∈ sectorCore Hs D₂ D n := by sorry

-- Prove2me | Theorems.Thm_BookProof_PermSector_purePow_mem_corePow
-- name    : BookProof.PermSector.purePow_mem_corePow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:51.639991+00:00
-- url     : https://prove2.me/theorems/3d29d822-e1ec-4aa3-9d36-bdf6a4f4b4fd
-- title:
--   `BookProof.PermSector.purePow_mem_corePow` : ∀ (n : ℕ) (f : Fin n → D₂), (∀ i, ((f i : Hs.carrier)) ∈ D) → purePow (domSpace Hs D₂) n f ∈ corePow Hs D₂ D n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.purePow_mem_corePow` : ∀ (n : ℕ) (f : Fin n → D₂), (∀ i, ((f i : Hs.carrier)) ∈ D) → purePow (domSpace Hs D₂) n f ∈ corePow Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.purePow_mem_corePow`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.purePow_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.purePow_mem_corePow : ∀ (n : ℕ) (f : Fin n → D₂),
    (∀ i, ((f i : Hs.carrier)) ∈ D) →
      purePow (domSpace Hs D₂) n f ∈ corePow Hs D₂ D n := by sorry

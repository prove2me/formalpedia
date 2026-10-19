-- Prove2me | Theorems.Thm_BookProof_PermSector_good_swap0
-- name    : BookProof.PermSector.good_swap0
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:44:18.094723+00:00
-- url     : https://prove2.me/theorems/d58a9fed-72e0-466f-8016-96ecd64483ab
-- title:
--   `BookProof.PermSector.good_swap0` : ∀ (n : ℕ) (p : Fin (n + 1)), Good Hs D₂ A D (n + 1) (swap0 (domSpace Hs D₂) (n + 1) p) (swap0 Hs (n + 1) p)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.good_swap0` : ∀ (n : ℕ) (p : Fin (n + 1)), Good Hs D₂ A D (n + 1) (swap0 (domSpace Hs D₂) (n + 1) p) (swap0 Hs (n + 1) p)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.good_swap0`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_swap0
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

theorem BookProof.PermSector.good_swap0 : ∀ (n : ℕ) (p : Fin (n + 1)),
    Good Hs D₂ A D (n + 1) (swap0 (domSpace Hs D₂) (n + 1) p) (swap0 Hs (n + 1) p) := by sorry

-- Prove2me | Theorems.Thm_BookProof_PermSector_good_swapFirst
-- name    : BookProof.PermSector.good_swapFirst
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T18:05:14.625001+00:00
-- url     : https://prove2.me/theorems/5084f35b-c64f-4427-8bf0-06169a14282c
-- title:
--   `BookProof.PermSector.good_swapFirst` (n : ℕ) : Good Hs D₂ A D (n + 2) (swapFirst (domSpace Hs D₂) n) (swapFirst Hs n) where incl t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.good_swapFirst` (n : ℕ) : Good Hs D₂ A D (n + 2) (swapFirst (domSpace Hs D₂) n) (swapFirst Hs n) where incl t
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.good_swapFirst`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_swapFirst
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.good_swapFirst (n : ℕ) :
    Good Hs D₂ A D (n + 2) (swapFirst (domSpace Hs D₂) n) (swapFirst Hs n) := by sorry

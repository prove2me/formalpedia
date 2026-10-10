-- Prove2me | Theorems.Thm_BookProof_PermSector_inclPow_purePow
-- name    : BookProof.PermSector.inclPow_purePow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:44.67705+00:00
-- url     : https://prove2.me/theorems/f240ace8-cd83-468b-9254-c408008fb24e
-- title:
--   `BookProof.PermSector.inclPow_purePow` : ∀ (n : ℕ) (f : Fin n → D₂), inclPow Hs D₂ n (purePow (domSpace Hs D₂) n f) = purePow Hs n (fun i => ((f i : Hs.carrier)))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.inclPow_purePow` : ∀ (n : ℕ) (f : Fin n → D₂), inclPow Hs D₂ n (purePow (domSpace Hs D₂) n f) = purePow Hs n (fun i => ((f i : Hs.carrier)))
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.inclPow_purePow`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.inclPow_purePow
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

theorem BookProof.PermSector.inclPow_purePow : ∀ (n : ℕ) (f : Fin n → D₂),
    inclPow Hs D₂ n (purePow (domSpace Hs D₂) n f)
      = purePow Hs n (fun i => ((f i : Hs.carrier))) := by sorry

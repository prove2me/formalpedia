-- Prove2me | Theorems.Thm_BookProof_PermSector_good_liftTail
-- name    : BookProof.PermSector.good_liftTail
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-09T18:04:34.30891+00:00
-- url     : https://prove2.me/theorems/1ca32f8c-1458-4f45-9bd2-0b7d4bd7c48f
-- title:
--   `BookProof.PermSector.good_liftTail` {n : ℕ} {uD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier} {uH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.good_liftTail` {n : ℕ} {uD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier} {uH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow n).carrier} (h : Good Hs D₂ A D n uD uH) : Good Hs D₂ A D (n + 1) (liftTail (domSpace Hs D₂) uD) (liftTail Hs uH) where incl t
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.good_liftTail`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_liftTail
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterVielbeinFiberFock
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.good_liftTail {n : ℕ}
    {uD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier}
    {uH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow n).carrier} (h : Good Hs D₂ A D n uD uH) :
    Good Hs D₂ A D (n + 1) (liftTail (domSpace Hs D₂) uD) (liftTail Hs uH) := by sorry

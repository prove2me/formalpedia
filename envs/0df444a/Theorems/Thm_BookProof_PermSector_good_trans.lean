-- Prove2me | Theorems.Thm_BookProof_PermSector_good_trans
-- name    : BookProof.PermSector.good_trans
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T18:04:28.176466+00:00
-- url     : https://prove2.me/theorems/6233668c-c75f-453a-8e70-909cbf6fc615
-- title:
--   `BookProof.PermSector.good_trans` {n : ℕ} {uD vD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier} {uH vH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.good_trans` {n : ℕ} {uD vD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier} {uH vH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow n).carrier} (hu : Good Hs D₂ A D n uD uH) (hv : Good Hs D₂ A D n vD vH) : Good Hs D₂ A D n (uD.trans vD) (uH.trans vH) where incl t
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.good_trans`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_trans
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

theorem BookProof.PermSector.good_trans {n : ℕ}
    {uD vD : ((domSpace Hs D₂).pow n).carrier ≃ₗᵢ[ℂ] ((domSpace Hs D₂).pow n).carrier}
    {uH vH : (Hs.pow n).carrier ≃ₗᵢ[ℂ] (Hs.pow n).carrier}
    (hu : Good Hs D₂ A D n uD uH) (hv : Good Hs D₂ A D n vD vH) :
    Good Hs D₂ A D n (uD.trans vD) (uH.trans vH) := by sorry

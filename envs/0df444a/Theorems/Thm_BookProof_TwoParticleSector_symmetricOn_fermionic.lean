-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_symmetricOn_fermionic
-- name    : BookProof.TwoParticleSector.symmetricOn_fermionic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-23T23:26:45.033923+00:00
-- url     : https://prove2.me/theorems/2f0fe6a8-0ab1-43bf-b40a-64acb642b1b2
-- title:
--   `BookProof.TwoParticleSector.symmetricOn_fermionic` (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingPro
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.symmetricOn_fermionic` (hA : SymmetricOn D₂ A) : SymmetricOn (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_fermionicProj Hs) (commutes_asymProj (T := sectorOp Hs D₂ A 2) (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.symmetricOn_fermionic`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.symmetricOn_fermionic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_ReducedEsa_commutes_asymProj
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_fermionicProj
import Definitions.Def_ChapterPermutationSectorEsa
open BookProof.TensorCore
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TwoParticleSector.symmetricOn_fermionic (hA : SymmetricOn D₂ A) :
    @SymmetricOn ↥(sector (fermionicProj Hs)) _ _
      (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2))
      (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_fermionicProj Hs)
        (commutes_asymProj (T := sectorOp Hs D₂ A 2)
          (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A))) := by sorry

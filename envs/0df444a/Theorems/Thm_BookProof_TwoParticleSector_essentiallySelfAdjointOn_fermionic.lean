-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_essentiallySelfAdjointOn_fermionic
-- name    : BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-09T17:55:55.739011+00:00
-- url     : https://prove2.me/theorems/0b27648a-6fda-427e-a495-313c5cf3951f
-- title:
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic` (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (ferm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic` (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2)) (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_fermionicProj Hs) (commutes_asymProj (T := sectorOp Hs D₂ A 2) (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_fermionicProj
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_ReducedEsa_commutes_asymProj
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
import Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
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

theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) :
    EssentiallySelfAdjointOn (F := sector (fermionicProj Hs))
      (redDom (fermionicProj Hs) (sectorDom Hs D₂ 2))
      (redOp (sectorOp Hs D₂ A 2) (isReducingProjection_fermionicProj Hs)
        (commutes_asymProj (T := sectorOp Hs D₂ A 2)
          (hUD := fun _ hx => swapH_mem_sectorDom Hs D₂ hx) (sectorOp_swapH Hs D₂ A))) := by sorry

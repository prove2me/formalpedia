-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_essentiallySelfAdjointOn_fermionic_core
-- name    : BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T22:21:18.760081+00:00
-- url     : https://prove2.me/theorems/485ea5d9-ab09-41e7-90c5-6d15e0fcf631
-- title:
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core` (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : Essenti
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core` (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (fermionicProj Hs) (sectorCore Hs D₂ D 2)) (redOp (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)) (isReducingProjection_fermionicProj Hs) (commutes_asymProj (T := restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)) (hUD := fun _ hx => swapH_mem_sectorCore Hs D₂ D hx) (restrictOp_sectorOp_swapH Hs D₂ A D)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorCore
import Theorems.Thm_BookProof_TwoParticleSector_restrictOp_sectorOp_swapH
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_fermionicProj
import Theorems.Thm_BookProof_ReducedEsa_commutes_asymProj
open BookProof.DirectSumEsa
open BookProof.GraphCore
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

theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core (hcore : IsGraphCore D A)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) :
    EssentiallySelfAdjointOn (F := sector (fermionicProj Hs))
      (redDom (fermionicProj Hs) (sectorCore Hs D₂ D 2))
      (redOp (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
        (isReducingProjection_fermionicProj Hs)
        (commutes_asymProj
          (T := restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
          (hUD := fun _ hx => swapH_mem_sectorCore Hs D₂ D hx)
          (restrictOp_sectorOp_swapH Hs D₂ A D))) := by sorry

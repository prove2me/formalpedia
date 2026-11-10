-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_essentiallySelfAdjointOn_bosonic_core
-- name    : BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T22:21:20.626552+00:00
-- url     : https://prove2.me/theorems/bcd3a629-5b7b-47cb-a67f-d6632f4bb01d
-- title:
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core` (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : Essential
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core` (hcore : IsGraphCore D A) (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) : EssentiallySelfAdjointOn (redDom (bosonicProj Hs) (sectorCore Hs D₂ D 2)) (redOp (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)) (isReducingProjection_bosonicProj Hs) (commutes_symProj (T := restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)) (hUD := fun _ hx => swapH_mem_sectorCore Hs D₂ D hx) (restrictOp_sectorOp_swapH Hs D₂ A D)))
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core
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
import Theorems.Thm_BookProof_TwoParticleSector_isReducingProjection_bosonicProj
import Theorems.Thm_BookProof_ReducedEsa_commutes_symProj
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

theorem BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core (hcore : IsGraphCore D A)
    (hesa : EssentiallySelfAdjointOn (sectorDom Hs D₂ 2) (sectorOp Hs D₂ A 2)) :
    EssentiallySelfAdjointOn (F := sector (bosonicProj Hs))
      (redDom (bosonicProj Hs) (sectorCore Hs D₂ D 2))
      (redOp (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
        (isReducingProjection_bosonicProj Hs)
        (commutes_symProj
          (T := restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2))
          (hUD := fun _ hx => swapH_mem_sectorCore Hs D₂ D hx)
          (restrictOp_sectorOp_swapH Hs D₂ A D))) := by sorry

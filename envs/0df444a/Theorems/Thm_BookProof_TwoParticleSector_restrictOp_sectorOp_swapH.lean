-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_restrictOp_sectorOp_swapH
-- name    : BookProof.TwoParticleSector.restrictOp_sectorOp_swapH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-09T17:25:30.93421+00:00
-- url     : https://prove2.me/theorems/e506860f-1b97-4111-8a14-02b95c0f1903
-- title:
--   `BookProof.TwoParticleSector.restrictOp_sectorOp_swapH` (x : sectorCore Hs D₂ D 2) : restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2) ⟨swapH Hs (x : (Hs.pow 2).c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.restrictOp_sectorOp_swapH` (x : sectorCore Hs D₂ D 2) : restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2) ⟨swapH Hs (x : (Hs.pow 2).carrier), swapH_mem_sectorCore Hs D₂ D x.2⟩ = swapH Hs (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2) x)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.restrictOp_sectorOp_swapH`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.restrictOp_sectorOp_swapH
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TensorCore_sectorCore_le_sectorDom
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorCore
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

theorem BookProof.TwoParticleSector.restrictOp_sectorOp_swapH (x : sectorCore Hs D₂ D 2) :
    restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2)
        ⟨swapH Hs (x : (Hs.pow 2).carrier), swapH_mem_sectorCore Hs D₂ D x.2⟩
      = swapH Hs (restrictOp (sectorOp Hs D₂ A 2) (sectorCore_le_sectorDom Hs D₂ D 2) x) := by sorry

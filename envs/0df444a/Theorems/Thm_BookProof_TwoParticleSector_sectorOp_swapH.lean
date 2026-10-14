-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_sectorOp_swapH
-- name    : BookProof.TwoParticleSector.sectorOp_swapH
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:14:46.766423+00:00
-- url     : https://prove2.me/theorems/c7c89537-3447-445d-87c9-88889020473f
-- title:
--   `BookProof.TwoParticleSector.sectorOp_swapH` (x : sectorDom Hs D₂ 2) : sectorOp Hs D₂ A 2 ⟨swapH Hs (x : (Hs.pow 2).carrier), swapH_mem_sectorDom Hs D₂ x.2⟩ = swapH Hs (sectorOp Hs
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.sectorOp_swapH` (x : sectorDom Hs D₂ 2) : sectorOp Hs D₂ A 2 ⟨swapH Hs (x : (Hs.pow 2).carrier), swapH_mem_sectorDom Hs D₂ x.2⟩ = swapH Hs (sectorOp Hs D₂ A 2 x)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.sectorOp_swapH`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.sectorOp_swapH
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
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

theorem BookProof.TwoParticleSector.sectorOp_swapH (x : sectorDom Hs D₂ 2) :
    sectorOp Hs D₂ A 2 ⟨swapH Hs (x : (Hs.pow 2).carrier),
        swapH_mem_sectorDom Hs D₂ x.2⟩
      = swapH Hs (sectorOp Hs D₂ A 2 x) := by sorry

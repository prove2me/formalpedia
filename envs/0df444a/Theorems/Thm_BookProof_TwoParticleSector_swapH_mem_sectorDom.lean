-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorDom
-- name    : BookProof.TwoParticleSector.swapH_mem_sectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:25.112856+00:00
-- url     : https://prove2.me/theorems/3f8c014d-b8ea-47f2-ae31-76084892dd16
-- title:
--   `BookProof.TwoParticleSector.swapH_mem_sectorDom` {x : (Hs.pow 2).carrier} (hx : x ∈ sectorDom Hs D₂ 2) : swapH Hs x ∈ sectorDom Hs D₂ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapH_mem_sectorDom` {x : (Hs.pow 2).carrier} (hx : x ∈ sectorDom Hs D₂ 2) : swapH Hs x ∈ sectorDom Hs D₂ 2
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapH_mem_sectorDom`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_mem_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TensorCore
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)

theorem BookProof.TwoParticleSector.swapH_mem_sectorDom {x : (Hs.pow 2).carrier} (hx : x ∈ sectorDom Hs D₂ 2) :
    swapH Hs x ∈ sectorDom Hs D₂ 2 := by sorry

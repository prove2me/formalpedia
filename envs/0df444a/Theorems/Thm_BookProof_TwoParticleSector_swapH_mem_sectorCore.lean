-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapH_mem_sectorCore
-- name    : BookProof.TwoParticleSector.swapH_mem_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:06.705112+00:00
-- url     : https://prove2.me/theorems/8a53375f-8ec3-425f-8cb6-17b17212a9bc
-- title:
--   `BookProof.TwoParticleSector.swapH_mem_sectorCore` {x : (Hs.pow 2).carrier} (hx : x ∈ sectorCore Hs D₂ D 2) : swapH Hs x ∈ sectorCore Hs D₂ D 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapH_mem_sectorCore` {x : (Hs.pow 2).carrier} (hx : x ∈ sectorCore Hs D₂ D 2) : swapH Hs x ∈ sectorCore Hs D₂ D 2
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapH_mem_sectorCore`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_mem_sectorCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
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

theorem BookProof.TwoParticleSector.swapH_mem_sectorCore {x : (Hs.pow 2).carrier} (hx : x ∈ sectorCore Hs D₂ D 2) :
    swapH Hs x ∈ sectorCore Hs D₂ D 2 := by sorry

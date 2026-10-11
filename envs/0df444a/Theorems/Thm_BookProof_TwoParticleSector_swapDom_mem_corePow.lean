-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapDom_mem_corePow
-- name    : BookProof.TwoParticleSector.swapDom_mem_corePow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:28:33.548979+00:00
-- url     : https://prove2.me/theorems/413e9d3b-f31f-46b1-95d8-e47a1b78000c
-- title:
--   `BookProof.TwoParticleSector.swapDom_mem_corePow` {t : ((domSpace Hs D₂).pow 2).carrier} (ht : t ∈ corePow Hs D₂ D 2) : swapDom Hs D₂ t ∈ corePow Hs D₂ D 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapDom_mem_corePow` {t : ((domSpace Hs D₂).pow 2).carrier} (ht : t ∈ corePow Hs D₂ D 2) : swapDom Hs D₂ t ∈ corePow Hs D₂ D 2
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapDom_mem_corePow`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapDom_mem_corePow
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
variable (D : Submodule ℂ Hs.carrier)

theorem BookProof.TwoParticleSector.swapDom_mem_corePow {t : ((domSpace Hs D₂).pow 2).carrier}
    (ht : t ∈ corePow Hs D₂ D 2) : swapDom Hs D₂ t ∈ corePow Hs D₂ D 2 := by sorry

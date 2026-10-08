-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_inclPow_swapDom
-- name    : BookProof.TwoParticleSector.inclPow_swapDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:58:10.3927+00:00
-- url     : https://prove2.me/theorems/91c6f06b-4a8c-4601-967d-6042b7d7df19
-- title:
--   `BookProof.TwoParticleSector.inclPow_swapDom` (t : ((domSpace Hs D₂).pow 2).carrier) : inclPow Hs D₂ 2 (swapDom Hs D₂ t) = swapH Hs (inclPow Hs D₂ 2 t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.inclPow_swapDom` (t : ((domSpace Hs D₂).pow 2).carrier) : inclPow Hs D₂ 2 (swapDom Hs D₂ t) = swapH Hs (inclPow Hs D₂ 2 t)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.inclPow_swapDom`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.inclPow_swapDom
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

theorem BookProof.TwoParticleSector.inclPow_swapDom (t : ((domSpace Hs D₂).pow 2).carrier) :
    inclPow Hs D₂ 2 (swapDom Hs D₂ t) = swapH Hs (inclPow Hs D₂ 2 t) := by sorry

-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_derPow_swapDom
-- name    : BookProof.TwoParticleSector.derPow_swapDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:52.509266+00:00
-- url     : https://prove2.me/theorems/7c0d0d57-1243-4e11-a64c-9e32ffada574
-- title:
--   `BookProof.TwoParticleSector.derPow_swapDom` (t : ((domSpace Hs D₂).pow 2).carrier) : derPow Hs D₂ A 2 (swapDom Hs D₂ t) = swapH Hs (derPow Hs D₂ A 2 t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.derPow_swapDom` (t : ((domSpace Hs D₂).pow 2).carrier) : derPow Hs D₂ A 2 (swapDom Hs D₂ t) = swapH Hs (derPow Hs D₂ A 2 t)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.derPow_swapDom`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.derPow_swapDom
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

theorem BookProof.TwoParticleSector.derPow_swapDom (t : ((domSpace Hs D₂).pow 2).carrier) :
    derPow Hs D₂ A 2 (swapDom Hs D₂ t) = swapH Hs (derPow Hs D₂ A 2 t) := by sorry

-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapTwo_inner
-- name    : BookProof.TwoParticleSector.swapTwo_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:29.412867+00:00
-- url     : https://prove2.me/theorems/28dedf8e-536c-4d32-9af7-a0b80f7ef2e8
-- title:
--   `BookProof.TwoParticleSector.swapTwo_inner` (t s : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : (inner ℂ (swapTwo X t) (swapTwo X s) : ℂ) = inner ℂ t s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapTwo_inner` (t s : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : (inner ℂ (swapTwo X t) (swapTwo X s) : ℂ) = inner ℂ t s
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapTwo_inner`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapTwo_inner
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterTensorGraphCore
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
open BookProof.TwoParticleSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}

theorem BookProof.TwoParticleSector.swapTwo_inner (t s : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) :
    (inner ℂ (swapTwo X t) (swapTwo X s) : ℂ) = inner ℂ t s := by sorry

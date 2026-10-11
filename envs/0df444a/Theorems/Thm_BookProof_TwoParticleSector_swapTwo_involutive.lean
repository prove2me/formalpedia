-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapTwo_involutive
-- name    : BookProof.TwoParticleSector.swapTwo_involutive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T16:27:47.237984+00:00
-- url     : https://prove2.me/theorems/ac3156b9-d9d4-4f40-8a70-c7f2f1b610c8
-- title:
--   `BookProof.TwoParticleSector.swapTwo_involutive` (t : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : swapTwo X (swapTwo X t) = t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapTwo_involutive` (t : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : swapTwo X (swapTwo X t) = t
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapTwo_involutive`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapTwo_involutive
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

theorem BookProof.TwoParticleSector.swapTwo_involutive (t : X ⊗[ℂ] (X ⊗[ℂ] ℂ)) : swapTwo X (swapTwo X t) = t := by sorry

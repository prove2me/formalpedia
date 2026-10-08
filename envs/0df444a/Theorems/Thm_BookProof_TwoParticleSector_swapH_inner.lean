-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapH_inner
-- name    : BookProof.TwoParticleSector.swapH_inner
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:53.339226+00:00
-- url     : https://prove2.me/theorems/282d2d2a-3764-4546-a406-06099307d69c
-- title:
--   `BookProof.TwoParticleSector.swapH_inner` (t s : (Hs.pow 2).carrier) : (inner ℂ (swapH Hs t) (swapH Hs s) : ℂ) = inner ℂ t s
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapH_inner` (t s : (Hs.pow 2).carrier) : (inner ℂ (swapH Hs t) (swapH Hs s) : ℂ) = inner ℂ t s
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapH_inner`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_inner
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

theorem BookProof.TwoParticleSector.swapH_inner (t s : (Hs.pow 2).carrier) :
    (inner ℂ (swapH Hs t) (swapH Hs s) : ℂ) = inner ℂ t s := by sorry

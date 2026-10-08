-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_swapH_involutive
-- name    : BookProof.TwoParticleSector.swapH_involutive
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:48.144975+00:00
-- url     : https://prove2.me/theorems/11065a9f-431c-4c25-ad5d-5345a7b3a441
-- title:
--   `BookProof.TwoParticleSector.swapH_involutive` (t : (Hs.pow 2).carrier) : swapH Hs (swapH Hs t) = t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.swapH_involutive` (t : (Hs.pow 2).carrier) : swapH Hs (swapH Hs t) = t
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.swapH_involutive`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.swapH_involutive
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

theorem BookProof.TwoParticleSector.swapH_involutive (t : (Hs.pow 2).carrier) : swapH Hs (swapH Hs t) = t := by sorry

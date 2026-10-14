-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_mem_bosonic_iff
-- name    : BookProof.TwoParticleSector.mem_bosonic_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:02.87971+00:00
-- url     : https://prove2.me/theorems/11431ac1-7d04-42de-83ff-03dd1459883e
-- title:
--   `BookProof.TwoParticleSector.mem_bosonic_iff` {x : (Hs.pow 2).carrier} : x ∈ sector (bosonicProj Hs) ↔ swapH Hs x = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.mem_bosonic_iff` {x : (Hs.pow 2).carrier} : x ∈ sector (bosonicProj Hs) ↔ swapH Hs x = x
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.mem_bosonic_iff`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.mem_bosonic_iff
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

theorem BookProof.TwoParticleSector.mem_bosonic_iff {x : (Hs.pow 2).carrier} :
    x ∈ sector (bosonicProj Hs) ↔ swapH Hs x = x := by sorry

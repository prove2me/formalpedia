-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_mem_fermionic_iff
-- name    : BookProof.TwoParticleSector.mem_fermionic_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:29:08.591193+00:00
-- url     : https://prove2.me/theorems/9b99999a-0343-4edc-90c3-78c4ec18e303
-- title:
--   `BookProof.TwoParticleSector.mem_fermionic_iff` {x : (Hs.pow 2).carrier} : x ∈ sector (fermionicProj Hs) ↔ swapH Hs x = -x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.mem_fermionic_iff` {x : (Hs.pow 2).carrier} : x ∈ sector (fermionicProj Hs) ↔ swapH Hs x = -x
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.mem_fermionic_iff`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.mem_fermionic_iff
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

theorem BookProof.TwoParticleSector.mem_fermionic_iff {x : (Hs.pow 2).carrier} :
    x ∈ sector (fermionicProj Hs) ↔ swapH Hs x = -x := by sorry

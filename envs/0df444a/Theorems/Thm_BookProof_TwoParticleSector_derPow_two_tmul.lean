-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_derPow_two_tmul
-- name    : BookProof.TwoParticleSector.derPow_two_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:51:47.440138+00:00
-- url     : https://prove2.me/theorems/3090a86a-bedf-4b25-a601-a132ff0198f2
-- title:
--   `BookProof.TwoParticleSector.derPow_two_tmul` (a b : D₂) (c : ℂ) : derPow Hs D₂ A 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier) = (A a) ⊗ₜ[ℂ] ((b :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.derPow_two_tmul` (a b : D₂) (c : ℂ) : derPow Hs D₂ A 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier) = (A a) ⊗ₜ[ℂ] ((b : Hs.carrier) ⊗ₜ[ℂ] c) + (a : Hs.carrier) ⊗ₜ[ℂ] ((A b) ⊗ₜ[ℂ] c)
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.derPow_two_tmul`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.derPow_two_tmul
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

theorem BookProof.TwoParticleSector.derPow_two_tmul (a b : D₂) (c : ℂ) :
    derPow Hs D₂ A 2 (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c) : ((domSpace Hs D₂).pow 2).carrier)
      = (A a) ⊗ₜ[ℂ] ((b : Hs.carrier) ⊗ₜ[ℂ] c)
        + (a : Hs.carrier) ⊗ₜ[ℂ] ((A b) ⊗ₜ[ℂ] c) := by sorry

-- Prove2me | Theorems.Thm_BookProof_TwoParticleSector_exists_ne_zero_fermionic
-- name    : BookProof.TwoParticleSector.exists_ne_zero_fermionic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:28:45.555977+00:00
-- url     : https://prove2.me/theorems/b7e92d22-a2e3-466c-a0d4-f1dfd6e38dc8
-- title:
--   `BookProof.TwoParticleSector.exists_ne_zero_fermionic` (hD : D ≤ D₂) {a b : Hs.carrier} (haD : a ∈ D) (hbD : b ∈ D) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : (inner ℂ a b : ℂ) = 0) : ∃ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterTwoParticleSectorEsa`.
--
--   `BookProof.TwoParticleSector.exists_ne_zero_fermionic` (hD : D ≤ D₂) {a b : Hs.carrier} (haD : a ∈ D) (hbD : b ∈ D) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : (inner ℂ a b : ℂ) = 0) : ∃ x : redDom (fermionicProj Hs) (sectorCore Hs D₂ D 2), x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.TwoParticleSector.exists_ne_zero_fermionic`.

-- Generated from ChapterTwoParticleSectorEsa.lean — theorem BookProof.TwoParticleSector.exists_ne_zero_fermionic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
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

theorem BookProof.TwoParticleSector.exists_ne_zero_fermionic (hD : D ≤ D₂) {a b : Hs.carrier} (haD : a ∈ D) (hbD : b ∈ D)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : (inner ℂ a b : ℂ) = 0) :
    ∃ x : redDom (fermionicProj Hs) (sectorCore Hs D₂ D 2), x ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_PermSector_exists_ne_zero_fermionic
-- name    : BookProof.PermSector.exists_ne_zero_fermionic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:19.050279+00:00
-- url     : https://prove2.me/theorems/b4a6fde2-d8b9-48e2-848c-17240537498f
-- title:
--   `BookProof.PermSector.exists_ne_zero_fermionic` (n : ℕ) (hD : D ≤ D₂) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.exists_ne_zero_fermionic` (n : ℕ) (hD : D ≤ D₂) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) : ∃ x : redDom (fermionicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.exists_ne_zero_fermionic`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.exists_ne_zero_fermionic
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.DirectSumEsa
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.exists_ne_zero_fermionic (n : ℕ) (hD : D ≤ D₂) (f : Fin n → Hs.carrier)
    (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0)
    (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : redDom (fermionicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0 := by sorry

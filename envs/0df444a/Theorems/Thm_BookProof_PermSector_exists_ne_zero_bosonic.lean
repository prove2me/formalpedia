-- Prove2me | Theorems.Thm_BookProof_PermSector_exists_ne_zero_bosonic
-- name    : BookProof.PermSector.exists_ne_zero_bosonic
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:25.90377+00:00
-- url     : https://prove2.me/theorems/b6746d07-4b18-403a-b29f-d6eae215e631
-- title:
--   `BookProof.PermSector.exists_ne_zero_bosonic` (n : ℕ) (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.exists_ne_zero_bosonic` (n : ℕ) (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.exists_ne_zero_bosonic`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.exists_ne_zero_bosonic
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

theorem BookProof.PermSector.exists_ne_zero_bosonic (n : ℕ) (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) : ∃ x : redDom (bosonicProj Hs n) (sectorCore Hs D₂ D n), x ≠ 0 := by sorry

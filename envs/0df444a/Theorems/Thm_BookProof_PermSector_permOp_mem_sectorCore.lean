-- Prove2me | Theorems.Thm_BookProof_PermSector_permOp_mem_sectorCore
-- name    : BookProof.PermSector.permOp_mem_sectorCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T17:08:27.540072+00:00
-- url     : https://prove2.me/theorems/db832b87-c1f4-4c48-9f21-c553eda0dce9
-- title:
--   `BookProof.PermSector.permOp_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier} (hx : x ∈ sectorCore Hs D₂ D n) : permOp Hs n σ x ∈ sectorCore Hs D₂ D n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permOp_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier} (hx : x ∈ sectorCore Hs D₂ D n) : permOp Hs n σ x ∈ sectorCore Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permOp_mem_sectorCore`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permOp_mem_sectorCore
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

theorem BookProof.PermSector.permOp_mem_sectorCore (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier}
    (hx : x ∈ sectorCore Hs D₂ D n) : permOp Hs n σ x ∈ sectorCore Hs D₂ D n := by sorry

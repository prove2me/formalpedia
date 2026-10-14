-- Prove2me | Theorems.Thm_BookProof_PermSector_corePow_permOp
-- name    : BookProof.PermSector.corePow_permOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:34.579282+00:00
-- url     : https://prove2.me/theorems/ca485d35-c0ad-4652-9f4c-1a6e09718143
-- title:
--   `BookProof.PermSector.corePow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) {t : ((domSpace Hs D₂).pow n).carrier} (ht : t ∈ corePow Hs D₂ D n) : permOp (domSpace Hs D₂) n σ t ∈ corePow
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.corePow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) {t : ((domSpace Hs D₂).pow n).carrier} (ht : t ∈ corePow Hs D₂ D n) : permOp (domSpace Hs D₂) n σ t ∈ corePow Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.corePow_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.corePow_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.corePow_permOp (n : ℕ) (σ : Equiv.Perm (Fin n))
    {t : ((domSpace Hs D₂).pow n).carrier} (ht : t ∈ corePow Hs D₂ D n) :
    permOp (domSpace Hs D₂) n σ t ∈ corePow Hs D₂ D n := by sorry

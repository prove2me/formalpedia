-- Prove2me | Theorems.Thm_BookProof_PermSector_good_permOp
-- name    : BookProof.PermSector.good_permOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:16.913979+00:00
-- url     : https://prove2.me/theorems/56c4695e-c253-47f3-9052-69193806b18c
-- title:
--   `BookProof.PermSector.good_permOp` : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), Good Hs D₂ A D n (permOp (domSpace Hs D₂) n σ) (permOp Hs n σ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.good_permOp` : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)), Good Hs D₂ A D n (permOp (domSpace Hs D₂) n σ) (permOp Hs n σ)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.good_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.good_permOp
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

theorem BookProof.PermSector.good_permOp : ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
    Good Hs D₂ A D n (permOp (domSpace Hs D₂) n σ) (permOp Hs n σ) := by sorry

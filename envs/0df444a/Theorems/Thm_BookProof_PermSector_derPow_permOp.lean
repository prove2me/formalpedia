-- Prove2me | Theorems.Thm_BookProof_PermSector_derPow_permOp
-- name    : BookProof.PermSector.derPow_permOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:50:40.827972+00:00
-- url     : https://prove2.me/theorems/a9d55b48-de40-4ca0-9d74-8c618ee71701
-- title:
--   `BookProof.PermSector.derPow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ((domSpace Hs D₂).pow n).carrier) : derPow Hs D₂ A n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (der
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.derPow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ((domSpace Hs D₂).pow n).carrier) : derPow Hs D₂ A n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (derPow Hs D₂ A n t)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.derPow_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.derPow_permOp
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

theorem BookProof.PermSector.derPow_permOp (n : ℕ) (σ : Equiv.Perm (Fin n))
    (t : ((domSpace Hs D₂).pow n).carrier) :
    derPow Hs D₂ A n (permOp (domSpace Hs D₂) n σ t)
      = permOp Hs n σ (derPow Hs D₂ A n t) := by sorry

-- Prove2me | Theorems.Thm_BookProof_PermSector_inclPow_permOp
-- name    : BookProof.PermSector.inclPow_permOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:59:26.173868+00:00
-- url     : https://prove2.me/theorems/7a39b34f-95c6-4537-bb51-df2ffb8381c2
-- title:
--   `BookProof.PermSector.inclPow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ((domSpace Hs D₂).pow n).carrier) : inclPow Hs D₂ n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (inc
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.inclPow_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (t : ((domSpace Hs D₂).pow n).carrier) : inclPow Hs D₂ n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (inclPow Hs D₂ n t)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.inclPow_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.inclPow_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.inclPow_permOp (n : ℕ) (σ : Equiv.Perm (Fin n))
    (t : ((domSpace Hs D₂).pow n).carrier) :
    inclPow Hs D₂ n (permOp (domSpace Hs D₂) n σ t) = permOp Hs n σ (inclPow Hs D₂ n t) := by sorry

-- Prove2me | Theorems.Thm_BookProof_PermSector_sectorOp_permOp
-- name    : BookProof.PermSector.sectorOp_permOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:45:53.425219+00:00
-- url     : https://prove2.me/theorems/9310e2c8-ce50-4a64-8f97-a4af081700be
-- title:
--   `BookProof.PermSector.sectorOp_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨permOp Hs n σ (x : (Hs.pow n).carrier), permOp_mem_sectorDom H
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.sectorOp_permOp` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) : sectorOp Hs D₂ A n ⟨permOp Hs n σ (x : (Hs.pow n).carrier), permOp_mem_sectorDom Hs D₂ n σ x.2⟩ = permOp Hs n σ (sectorOp Hs D₂ A n x)
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.sectorOp_permOp`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.sectorOp_permOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
import Theorems.Thm_BookProof_PermSector_permOp_mem_sectorDom
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.sectorOp_permOp (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : sectorDom Hs D₂ n) :
    sectorOp Hs D₂ A n ⟨permOp Hs n σ (x : (Hs.pow n).carrier),
        permOp_mem_sectorDom Hs D₂ n σ x.2⟩
      = permOp Hs n σ (sectorOp Hs D₂ A n x) := by sorry

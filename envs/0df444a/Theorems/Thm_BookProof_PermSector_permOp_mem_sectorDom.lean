-- Prove2me | Theorems.Thm_BookProof_PermSector_permOp_mem_sectorDom
-- name    : BookProof.PermSector.permOp_mem_sectorDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:50.452964+00:00
-- url     : https://prove2.me/theorems/d522c004-ad38-4ed9-871f-ff96500d4bd0
-- title:
--   `BookProof.PermSector.permOp_mem_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier} (hx : x ∈ sectorDom Hs D₂ n) : permOp Hs n σ x ∈ sectorDom Hs D₂ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.permOp_mem_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier} (hx : x ∈ sectorDom Hs D₂ n) : permOp Hs n σ x ∈ sectorDom Hs D₂ n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.permOp_mem_sectorDom`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.permOp_mem_sectorDom
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

theorem BookProof.PermSector.permOp_mem_sectorDom (n : ℕ) (σ : Equiv.Perm (Fin n)) {x : (Hs.pow n).carrier}
    (hx : x ∈ sectorDom Hs D₂ n) : permOp Hs n σ x ∈ sectorDom Hs D₂ n := by sorry

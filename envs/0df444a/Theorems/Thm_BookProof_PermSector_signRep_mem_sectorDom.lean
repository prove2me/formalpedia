-- Prove2me | Theorems.Thm_BookProof_PermSector_signRep_mem_sectorDom
-- name    : BookProof.PermSector.signRep_mem_sectorDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T10:15:07.447113+00:00
-- url     : https://prove2.me/theorems/ef231e66-9b35-4b09-aca1-4baddb4193ff
-- title:
--   `BookProof.PermSector.signRep_mem_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorDom Hs D₂ n) : (signRep Hs n).act σ x ∈ sectorDom Hs D₂ n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.signRep_mem_sectorDom` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorDom Hs D₂ n) : (signRep Hs n).act σ x ∈ sectorDom Hs D₂ n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.signRep_mem_sectorDom`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.signRep_mem_sectorDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterTensorPermutation
import Mathlib
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterGaugeUnconstrainedSpectrum
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup
open BookProof.PermSector



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

theorem BookProof.PermSector.signRep_mem_sectorDom (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier)
    (hx : x ∈ sectorDom Hs D₂ n) : (signRep Hs n).act σ x ∈ sectorDom Hs D₂ n := by sorry

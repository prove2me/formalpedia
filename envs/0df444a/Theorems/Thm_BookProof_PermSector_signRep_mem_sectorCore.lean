-- Prove2me | Theorems.Thm_BookProof_PermSector_signRep_mem_sectorCore
-- name    : BookProof.PermSector.signRep_mem_sectorCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:44.603347+00:00
-- url     : https://prove2.me/theorems/2146c2fc-06bb-4ea0-96c8-a634f114e73d
-- title:
--   `BookProof.PermSector.signRep_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorCore Hs D₂ D n) : (signRep Hs n).act σ x ∈ sectorCore Hs D₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterPermutationSectorEsa`.
--
--   `BookProof.PermSector.signRep_mem_sectorCore` (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier) (hx : x ∈ sectorCore Hs D₂ D n) : (signRep Hs n).act σ x ∈ sectorCore Hs D₂ D n
--
--   Formalization note: Lean 4 identifier `BookProof.PermSector.signRep_mem_sectorCore`.

-- Generated from ChapterPermutationSectorEsa.lean — theorem BookProof.PermSector.signRep_mem_sectorCore
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
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.DirectSumEsa
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

theorem BookProof.PermSector.signRep_mem_sectorCore (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : (Hs.pow n).carrier)
    (hx : x ∈ sectorCore Hs D₂ D n) : (signRep Hs n).act σ x ∈ sectorCore Hs D₂ D n := by sorry

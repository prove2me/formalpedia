-- Prove2me | Theorems.Thm_BookProof_FockStatistics_mem_cfermionicSector_iff_inc
-- name    : BookProof.FockStatistics.mem_cfermionicSector_iff_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:01:28.250223+00:00
-- url     : https://prove2.me/theorems/e34ba4e9-3ef2-42c1-b802-4ec75f2f8dbd
-- title:
--   `BookProof.FockStatistics.mem_cfermionicSector_iff_inc` (n : ℕ) {x : fockSector Hs n} : x ∈ sector (cfermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (csignRep Hs n).act σ x = x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.mem_cfermionicSector_iff_inc` (n : ℕ) {x : fockSector Hs n} : x ∈ sector (cfermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (csignRep Hs n).act σ x = x
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.mem_cfermionicSector_iff_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_mem_cfermionicSector_iff`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.mem_cfermionicSector_iff_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterWignerOrbitClassification
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.TensorCore
open BookProof.ChapterWignerLittleGroup



open BookProof.ReducedEsa
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

theorem BookProof.FockStatistics.mem_cfermionicSector_iff_inc (n : ℕ) {x : fockSector Hs n} :
    x ∈ sector (cfermionicProj Hs n) ↔ ∀ σ : Equiv.Perm (Fin n), (csignRep Hs n).act σ x = x := by sorry

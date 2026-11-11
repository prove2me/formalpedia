-- Prove2me | Theorems.Thm_BookProof_FockStatistics_sectorEmb_apply_inc
-- name    : BookProof.FockStatistics.sectorEmb_apply_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:02:29.231626+00:00
-- url     : https://prove2.me/theorems/df0063c5-981c-4ebb-b37f-7e2cae30d013
-- title:
--   `BookProof.FockStatistics.sectorEmb_apply_inc` (n : ℕ) (x : (Hs.pow n).carrier) : sectorEmb Hs n x = (x : fockSector Hs n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.sectorEmb_apply_inc` (n : ℕ) (x : (Hs.pow n).carrier) : sectorEmb Hs n x = (x : fockSector Hs n)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.sectorEmb_apply_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_sectorEmb_apply`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.sectorEmb_apply_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.TensorCore



open BookProof.ReducedEsa
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

theorem BookProof.FockStatistics.sectorEmb_apply_inc (n : ℕ) (x : (Hs.pow n).carrier) :
    sectorEmb Hs n x = (x : fockSector Hs n) := by sorry

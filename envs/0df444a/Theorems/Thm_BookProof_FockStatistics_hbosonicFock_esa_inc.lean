-- Prove2me | Theorems.Thm_BookProof_FockStatistics_hbosonicFock_esa_inc
-- name    : BookProof.FockStatistics.hbosonicFock_esa_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:59:51.436377+00:00
-- url     : https://prove2.me/theorems/d01b769a-7617-48d9-bd87-19edf68e26de
-- title:
--   `BookProof.FockStatistics.hbosonicFock_esa_inc` : EssentiallySelfAdjointOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.hbosonicFock_esa_inc` : EssentiallySelfAdjointOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.hbosonicFock_esa_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_hbosonicFock_esa`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.hbosonicFock_esa_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
open BookProof.TensorCore



open BookProof.ReducedEsa
open BookProof.FarisLavine

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

include hdense hesa hsym in

theorem BookProof.FockStatistics.hbosonicFock_esa_inc :
    EssentiallySelfAdjointOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A) := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockStatistics_hbosonicFock_symmetricOn_inc
-- name    : BookProof.FockStatistics.hbosonicFock_symmetricOn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:00:15.781388+00:00
-- url     : https://prove2.me/theorems/de72a31c-3e1e-435f-a220-ba8fe1710b4b
-- title:
--   `BookProof.FockStatistics.hbosonicFock_symmetricOn_inc` : SymmetricOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.hbosonicFock_symmetricOn_inc` : SymmetricOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.hbosonicFock_symmetricOn_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_hbosonicFock_symmetricOn`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.hbosonicFock_symmetricOn_inc
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

include hsym in

theorem BookProof.FockStatistics.hbosonicFock_symmetricOn_inc :
    SymmetricOn (hbosonicFockDom Hs D) (hbosonicFockOp Hs D A) := by sorry

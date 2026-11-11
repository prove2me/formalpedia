-- Prove2me | Theorems.Thm_BookProof_FockStatistics_hfermionicFock_symmetricOn_inc
-- name    : BookProof.FockStatistics.hfermionicFock_symmetricOn_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:01:00.878803+00:00
-- url     : https://prove2.me/theorems/e6b78e5e-6601-4207-be94-7c893860c01d
-- title:
--   `BookProof.FockStatistics.hfermionicFock_symmetricOn_inc` : SymmetricOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.hfermionicFock_symmetricOn_inc` : SymmetricOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.hfermionicFock_symmetricOn_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_hfermionicFock_symmetricOn`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.hfermionicFock_symmetricOn_inc
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

theorem BookProof.FockStatistics.hfermionicFock_symmetricOn_inc :
    SymmetricOn (hfermionicFockDom Hs D) (hfermionicFockOp Hs D A) := by sorry

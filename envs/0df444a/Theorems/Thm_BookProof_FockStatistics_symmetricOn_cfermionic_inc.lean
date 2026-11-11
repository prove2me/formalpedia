-- Prove2me | Theorems.Thm_BookProof_FockStatistics_symmetricOn_cfermionic_inc
-- name    : BookProof.FockStatistics.symmetricOn_cfermionic_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T07:03:59.763885+00:00
-- url     : https://prove2.me/theorems/f2520c10-cd11-4ac5-9f03-4f03999d3d9b
-- title:
--   `BookProof.FockStatistics.symmetricOn_cfermionic_inc` (n : ℕ) : SymmetricOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n)) (cfermionicSectorOp Hs D A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.symmetricOn_cfermionic_inc` (n : ℕ) : SymmetricOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n)) (cfermionicSectorOp Hs D A n)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.symmetricOn_cfermionic_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_symmetricOn_cfermionic`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.symmetricOn_cfermionic_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterA
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterMaschkeFiniteGroup
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.TensorCore



open BookProof.ReducedEsa
open BookProof.FarisLavine
open BookProof.SecondQuantizationCore

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

include hsym in

theorem BookProof.FockStatistics.symmetricOn_cfermionic_inc (n : ℕ) :
    SymmetricOn (redDom (cfermionicProj Hs n) (fockSectorDom Hs D n))
      (cfermionicSectorOp Hs D A n) := by sorry

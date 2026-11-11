-- Prove2me | Theorems.Thm_BookProof_FockStatistics_essentiallySelfAdjointOn_cbosonic_inc
-- name    : BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:57:39.098946+00:00
-- url     : https://prove2.me/theorems/208a2cb9-e0e5-4313-9829-fa83cb3b120e
-- title:
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc` (n : ℕ) : EssentiallySelfAdjointOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n)) (cbosonicSectorOp Hs D A n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc` (n : ℕ) : EssentiallySelfAdjointOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n)) (cbosonicSectorOp Hs D A n)
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_essentiallySelfAdjointOn_cbosonic`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc
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

include hdense hesa hsym in

theorem BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic_inc (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n))
      (cbosonicSectorOp Hs D A n) := by sorry

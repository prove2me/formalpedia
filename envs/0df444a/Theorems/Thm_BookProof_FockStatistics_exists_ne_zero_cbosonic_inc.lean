-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_cbosonic_inc
-- name    : BookProof.FockStatistics.exists_ne_zero_cbosonic_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:58:48.373277+00:00
-- url     : https://prove2.me/theorems/f2db9679-ba65-41dd-924c-b25fca95b028
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_cbosonic_inc` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n), x ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_cbosonic_inc` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n), x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_cbosonic_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_exists_ne_zero_cbosonic`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_cbosonic_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
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

theorem BookProof.FockStatistics.exists_ne_zero_cbosonic_inc (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n), x ≠ 0 := by sorry

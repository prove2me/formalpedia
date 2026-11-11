-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_cfermionic_inc
-- name    : BookProof.FockStatistics.exists_ne_zero_cfermionic_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:59:00.652136+00:00
-- url     : https://prove2.me/theorems/d651d13a-13d7-4d14-9cd8-cfe8e2dc5fca
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_cfermionic_inc` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_cfermionic_inc` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) : ∃ x : redDom (cfermionicProj Hs n) (fockSectorDom Hs D n), x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_cfermionic_inc`.
--
--   Replaces the unuploadable node `BookProof_FockStatistics_exists_ne_zero_cfermionic`, whose statement name is already declared inside its published definition bundle; the `_inc` suffix publishes the same statement as its own node.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_cfermionic_inc
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

theorem BookProof.FockStatistics.exists_ne_zero_cfermionic_inc (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D)
    (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : redDom (cfermionicProj Hs n) (fockSectorDom Hs D n), x ≠ 0 := by sorry

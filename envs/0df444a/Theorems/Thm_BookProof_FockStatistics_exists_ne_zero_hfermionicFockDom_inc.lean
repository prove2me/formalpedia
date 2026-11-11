-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_hfermionicFockDom_inc
-- name    : BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:56:23.133195+00:00
-- url     : https://prove2.me/theorems/1340ca86-36d8-4f9e-a720-571332888903
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) : ∃ x : hfermionicFockDom Hs D, x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc`.
--
--   Replaces the published node `BookProof_FockStatistics_exists_ne_zero_hfermionicFockDom`, whose preamble declared the section `variable` block twice: Lean read the second `(Hs) (D) (A)` as new variables, so its target carried the hypotheses on one `(D, A)` and the conclusion on another and no proof could exist.  The `_inc` twin is the same statement with the re-declarations removed.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc
import Definitions.Def_ChapterReducingSubspaceEsa
import Mathlib
import Definitions.Def_ChapterFockStatisticsCompletion
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterFarisLavineCore
open BookProof.TensorCore



open BookProof.ReducedEsa
open BookProof.FarisLavine

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
variable [CompleteSpace Hs.carrier] (hdense : Dense (D : Set Hs.carrier))
  (hsym : SymmetricOn D A) (hesa : EssentiallySelfAdjointOn D A)

theorem BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom_inc (n : ℕ) (f : Fin n → Hs.carrier)
    (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0)
    (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : hfermionicFockDom Hs D, x ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_hbosonicFockDom_inc
-- name    : BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-10T06:56:24.245225+00:00
-- url     : https://prove2.me/theorems/1c0f2a9e-34ad-46d9-96e9-ced6eb4d0c8c
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : hbosonicFockDom Hs D, x ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : hbosonicFockDom Hs D, x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc`.
--
--   Replaces the published node `BookProof_FockStatistics_exists_ne_zero_hbosonicFockDom`, whose preamble declared the section `variable` block twice: Lean read the second `(Hs) (D) (A)` as new variables, so its target carried the hypotheses on one `(D, A)` and the conclusion on another and no proof could exist.  The `_inc` twin is the same statement with the re-declarations removed.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc
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

theorem BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom_inc (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : hbosonicFockDom Hs D, x ≠ 0 := by sorry

-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_hbosonicFockDom
-- name    : BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:42:16.478996+00:00
-- url     : https://prove2.me/theorems/081c8884-257c-4a7a-bff9-178c1aa54b53
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : hbosonicFockDom Hs D, x ≠ 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom` (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) : ∃ x : hbosonicFockDom Hs D, x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom`.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom
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
variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)
variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier)

theorem BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom (n : ℕ) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : hbosonicFockDom Hs D, x ≠ 0 := by sorry

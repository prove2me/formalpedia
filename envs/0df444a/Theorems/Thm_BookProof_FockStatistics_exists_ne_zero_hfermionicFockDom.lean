-- Prove2me | Theorems.Thm_BookProof_FockStatistics_exists_ne_zero_hfermionicFockDom
-- name    : BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T20:44:49.514039+00:00
-- url     : https://prove2.me/theorems/291b533b-4051-4063-aa2f-aeb03c12a85f
-- title:
--   `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockStatisticsCompletion`.
--
--   `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom` (n : ℕ) (f : Fin n → Hs.carrier) (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0) (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) : ∃ x : hfermionicFockDom Hs D, x ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom`.

-- Generated from ChapterFockStatisticsCompletion.lean — theorem BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom
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

theorem BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom (n : ℕ) (f : Fin n → Hs.carrier)
    (hfD : ∀ i, f i ∈ D) (hf0 : ∀ i, f i ≠ 0)
    (hortho : ∀ i j, i ≠ j → (inner ℂ (f i) (f j) : ℂ) = 0) :
    ∃ x : hfermionicFockDom Hs D, x ≠ 0 := by sorry

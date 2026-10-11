-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_exists_irreducible_decomposition
-- name    : BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:48:49.920973+00:00
-- url     : https://prove2.me/theorems/cf13e17a-ea60-4f1a-a48f-9e4c46a0baa3
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} (U : Submodule ℂ V) (hU : IsInvariant ρ U) : ∃ L : L
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} (U : Submodule ℂ V) (hU : IsInvariant ρ U) : ∃ L : List (Submodule ℂ V), (∀ W ∈ L, W ≤ U ∧ IsIrreducibleInvariant ρ W) ∧ L.foldr (· ⊔ ·) ⊥ = U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} (U : Submodule ℂ V) (hU : IsInvariant ρ U) :
    ∃ L : List (Submodule ℂ V),
      (∀ W ∈ L, W ≤ U ∧ IsIrreducibleInvariant ρ W) ∧
        L.foldr (· ⊔ ·) ⊥ = U := by sorry

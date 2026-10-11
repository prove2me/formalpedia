-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_exists_irreducible_invariant_le
-- name    : BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:49:42.981892+00:00
-- url     : https://prove2.me/theorems/7550a1e4-617a-466b-9c56-a1f18dbbba79
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {U : Submodule ℂ V} (hU : IsInvariant ρ U) (hUne : U
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {U : Submodule ℂ V} (hU : IsInvariant ρ U) (hUne : U ≠ ⊥) : ∃ W ≤ U, IsIrreducibleInvariant ρ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {U : Submodule ℂ V} (hU : IsInvariant ρ U) (hUne : U ≠ ⊥) :
    ∃ W ≤ U, IsIrreducibleInvariant ρ W := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_unitary_complete_reducibility
-- name    : BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:48:20.643873+00:00
-- url     : https://prove2.me/theorems/f3e23f0b-8378-4093-b7eb-4c03452b5c22
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) : ∃ W' : Sub
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility` [FiniteDimensional ℂ V] {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) : ∃ W' : Submodule ℂ V, IsInvariant ρ W' ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.unitary_complete_reducibility [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) :
    ∃ W' : Submodule ℂ V, IsInvariant ρ W' ∧ IsCompl W W' := by sorry

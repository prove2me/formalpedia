-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_inv_mem_of_isInvariant
-- name    : BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:48:27.941591+00:00
-- url     : https://prove2.me/theorems/d8fd7e84-09ee-47b2-a7ec-074547daa217
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant` {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (g : G) {x : V} (hx : x ∈ W) : (ρ g).symm x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant` {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (g : G) {x : V} (hx : x ∈ W) : (ρ g).symm x ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.inv_mem_of_isInvariant {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (g : G) {x : V} (hx : x ∈ W) : (ρ g).symm x ∈ W := by sorry

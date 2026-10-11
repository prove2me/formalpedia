-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_isInvariant_bot
-- name    : BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:48:32.027372+00:00
-- url     : https://prove2.me/theorems/f7f6d1f7-a217-4706-8808-c3681fff638a
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot` (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊥ : Submodule ℂ V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot` (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊥ : Submodule ℂ V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.isInvariant_bot (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊥ : Submodule ℂ V) := by sorry

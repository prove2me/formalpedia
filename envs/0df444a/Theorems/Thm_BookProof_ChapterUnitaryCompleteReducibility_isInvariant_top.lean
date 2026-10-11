-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_isInvariant_top
-- name    : BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:47:58.745977+00:00
-- url     : https://prove2.me/theorems/3fee9b75-c449-4dd3-9444-4f59259d229d
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top` (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊤ : Submodule ℂ V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top` (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊤ : Submodule ℂ V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.isInvariant_top (ρ : G →* (V ≃ₗᵢ[ℂ] V)) : IsInvariant ρ (⊤ : Submodule ℂ V) := by sorry

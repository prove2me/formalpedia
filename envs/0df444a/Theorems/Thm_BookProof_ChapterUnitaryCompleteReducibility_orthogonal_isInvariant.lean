-- Prove2me | Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_orthogonal_isInvariant
-- name    : BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:48:17.633313+00:00
-- url     : https://prove2.me/theorems/1cfc6ab9-e905-4ae3-bef0-b0b83748b0f9
-- title:
--   `BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant` {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) : IsInvariant ρ Wᗮ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterUnitaryCompleteReducibility`.
--
--   `BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant` {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V} (hW : IsInvariant ρ W) : IsInvariant ρ Wᗮ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant`.

-- Generated from ChapterUnitaryCompleteReducibility.lean — theorem BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility



open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterUnitaryCompleteReducibility.orthogonal_isInvariant {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) : IsInvariant ρ Wᗮ := by sorry

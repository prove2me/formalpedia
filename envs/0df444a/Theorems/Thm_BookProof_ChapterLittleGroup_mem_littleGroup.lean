-- Prove2me | Theorems.Thm_BookProof_ChapterLittleGroup_mem_littleGroup
-- name    : BookProof.ChapterLittleGroup.mem_littleGroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:31:06.099773+00:00
-- url     : https://prove2.me/theorems/3b93c38f-0b7a-42a2-84ff-2da742934736
-- title:
--   `BookProof.ChapterLittleGroup.mem_littleGroup` {q : K → G} {l₀ : K} {g : G} : g ∈ littleGroup q l₀ ↔ q l₀ * g = g * q l₀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLittleGroup`.
--
--   `BookProof.ChapterLittleGroup.mem_littleGroup` {q : K → G} {l₀ : K} {g : G} : g ∈ littleGroup q l₀ ↔ q l₀ * g = g * q l₀
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLittleGroup.mem_littleGroup`.

-- Generated from ChapterLittleGroup.lean — theorem BookProof.ChapterLittleGroup.mem_littleGroup
import Mathlib
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup



variable {G : Type*} [Group G] {K : Type*}

theorem BookProof.ChapterLittleGroup.mem_littleGroup {q : K → G} {l₀ : K} {g : G} :
    g ∈ littleGroup q l₀ ↔ q l₀ * g = g * q l₀ := by sorry

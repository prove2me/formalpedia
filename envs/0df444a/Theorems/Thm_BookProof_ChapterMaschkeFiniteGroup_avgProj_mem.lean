-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_mem
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:58:40.32466+00:00
-- url     : https://prove2.me/theorems/52a380ec-4ab6-48b8-9e7a-94ca95b4992b
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_mem` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x, pi x ∈ W) (x : V) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_mem` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x, pi x ∈ W) (x : V) : avgProj ρ pi x ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_mem`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_mem
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_mem [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x, pi x ∈ W) (x : V) : avgProj ρ pi x ∈ W := by sorry

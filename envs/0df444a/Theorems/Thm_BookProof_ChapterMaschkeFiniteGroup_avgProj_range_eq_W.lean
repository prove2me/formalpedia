-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_range_eq_W
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:59:09.487046+00:00
-- url     : https://prove2.me/theorems/76885ca5-3357-41ec-b2fd-e842968b7d53
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W) (hpi_id : ∀ x ∈ W, pi x = x) : LinearMap.range (avgProj ρ pi) = W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_range_eq_W [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W)
    (hpi_id : ∀ x ∈ W, pi x = x) :
    LinearMap.range (avgProj ρ pi) = W := by sorry

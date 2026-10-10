-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_idempotent
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:59:02.313924+00:00
-- url     : https://prove2.me/theorems/dbd861ed-88d5-46bf-bdb4-e3a0221dcf4d
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W) (hpi_id : ∀ x ∈ W, pi x = x) (x : V) : avgProj ρ pi (avgProj ρ pi x) = avgProj ρ pi x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_idempotent [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi_mem : ∀ x, pi x ∈ W)
    (hpi_id : ∀ x ∈ W, pi x = x) (x : V) :
    avgProj ρ pi (avgProj ρ pi x) = avgProj ρ pi x := by sorry

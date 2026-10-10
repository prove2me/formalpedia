-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_eq_self
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:58:40.569987+00:00
-- url     : https://prove2.me/theorems/9449447a-e64d-43af-9637-7b46262e01e0
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x ∈ W, pi x = x) {
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self` [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V} (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x ∈ W, pi x = x) {x : V} (hx : x ∈ W) : avgProj ρ pi x = x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_eq_self [Fintype G] {ρ : Representation ℂ G V} {W : Submodule ℂ V}
    (hW : IsInvariant ρ W) (pi : V →ₗ[ℂ] V) (hpi : ∀ x ∈ W, pi x = x) {x : V} (hx : x ∈ W) :
    avgProj ρ pi x = x := by sorry

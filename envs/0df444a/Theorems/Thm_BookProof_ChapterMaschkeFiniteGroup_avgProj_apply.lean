-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_apply
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:58:17.592412+00:00
-- url     : https://prove2.me/theorems/2fd903de-5ddf-43d3-a57c-0796631ed926
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_apply` [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (x : V) : avgProj ρ pi x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (pi (ρ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_apply` [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (x : V) : avgProj ρ pi x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (pi (ρ g⁻¹ x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_apply`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_apply
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_apply [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (x : V) :
    avgProj ρ pi x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (pi (ρ g⁻¹ x)) := by sorry

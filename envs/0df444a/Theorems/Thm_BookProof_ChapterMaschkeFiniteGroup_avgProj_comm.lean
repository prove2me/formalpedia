-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_avgProj_comm
-- name    : BookProof.ChapterMaschkeFiniteGroup.avgProj_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:58:41.508305+00:00
-- url     : https://prove2.me/theorems/badb886c-7e20-40f9-8253-9f1f52c356cb
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_comm` [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (h : G) (x : V) : avgProj ρ pi (ρ h x) = ρ h (avgProj ρ pi x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.avgProj_comm` [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (h : G) (x : V) : avgProj ρ pi (ρ h x) = ρ h (avgProj ρ pi x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.avgProj_comm`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_comm
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.avgProj_comm [Fintype G] (ρ : Representation ℂ G V) (pi : V →ₗ[ℂ] V) (h : G) (x : V) :
    avgProj ρ pi (ρ h x) = ρ h (avgProj ρ pi x) := by sorry

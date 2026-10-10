-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_maschke_decomposition
-- name    : BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:59:27.394983+00:00
-- url     : https://prove2.me/theorems/a3da7180-0169-4f31-876c-87adb67c75a8
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition` [Finite G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) : ∃ (W' : Submo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition` [Finite G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) : ∃ (W' : Submodule ℂ V) (p : V →ₗ[ℂ] V), IsInvariant ρ W' ∧ IsCompl W W' ∧ (∀ x, p (p x) = p x) ∧ LinearMap.range p = W ∧ LinearMap.ker p = W' ∧ (∀ (g : G) (x : V), p (ρ g x) = ρ g (p x))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.maschke_decomposition [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) :
    ∃ (W' : Submodule ℂ V) (p : V →ₗ[ℂ] V),
      IsInvariant ρ W' ∧ IsCompl W W' ∧ (∀ x, p (p x) = p x) ∧
        LinearMap.range p = W ∧ LinearMap.ker p = W' ∧
        (∀ (g : G) (x : V), p (ρ g x) = ρ g (p x)) := by sorry

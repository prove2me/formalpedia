-- Prove2me | Theorems.Thm_BookProof_ChapterMaschkeFiniteGroup_maschke_invariant_complement
-- name    : BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:59:22.092148+00:00
-- url     : https://prove2.me/theorems/6c45050f-c306-4c65-b799-b7da823f748f
-- title:
--   `BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement` [Finite G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) : ∃ W' :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMaschkeFiniteGroup`.
--
--   `BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement` [Finite G] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) : ∃ W' : Submodule ℂ V, IsInvariant ρ W' ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement`.

-- Generated from ChapterMaschkeFiniteGroup.lean — theorem BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement
import Mathlib
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterMaschkeFiniteGroup



variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterMaschkeFiniteGroup.maschke_invariant_complement [Finite G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (W : Submodule ℂ V) (hW : IsInvariant ρ W) :
    ∃ W' : Submodule ℂ V, IsInvariant ρ W' ∧ IsCompl W W' := by sorry

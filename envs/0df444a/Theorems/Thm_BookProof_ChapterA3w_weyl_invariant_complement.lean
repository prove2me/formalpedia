-- Prove2me | Theorems.Thm_BookProof_ChapterA3w_weyl_invariant_complement
-- name    : BookProof.ChapterA3w.weyl_invariant_complement
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:37:58.968951+00:00
-- url     : https://prove2.me/theorems/334fd78c-a076-4a83-b01d-4177c2f3b067
-- title:
--   `BookProof.ChapterA3w.weyl_invariant_complement` (h : WeylCompleteReducibility) {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ (Matrix.SpecialLi
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA3w`.
--
--   `BookProof.ChapterA3w.weyl_invariant_complement` (h : WeylCompleteReducibility) {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V] (ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V) (W : Submodule ℂ V) (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W, ρ g x ∈ W) : ∃ W' : Submodule ℂ V, (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA3w.weyl_invariant_complement`.

-- Generated from ChapterA3w.lean — theorem BookProof.ChapterA3w.weyl_invariant_complement
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterA3j
import Definitions.Def_ChapterA3k
import Definitions.Def_ChapterA3q
import Mathlib
import Definitions.Def_ChapterA3w
open BookProof.ChapterA3w


open Matrix


open BookProof.ChapterA3 BookProof.ChapterA3j BookProof.ChapterA3k BookProof.ChapterA3q

theorem BookProof.ChapterA3w.weyl_invariant_complement (h : WeylCompleteReducibility)
    {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V)
    (W : Submodule ℂ V)
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W' : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W' := by sorry

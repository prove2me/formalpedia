-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_weyl_complete_reducibility_SL2
-- name    : BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:26.1874+00:00
-- url     : https://prove2.me/theorems/5f1690d5-b6fe-4253-9935-d2f4194e284c
-- title:
--   `BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2` [FiniteDimensional ℂ V] (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2` [FiniteDimensional ℂ V] (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ W, rho g v ∈ W) : ∃ U : Submodule ℂ V, (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ U, rho g v ∈ U) ∧ IsCompl W U
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem BookProof.ChapterWeylSL2Group.weyl_complete_reducibility_SL2 [FiniteDimensional ℂ V]
    (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V}
    (hW : ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ W, rho g v ∈ W) :
    ∃ U : Submodule ℂ V,
      (∀ g : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ v ∈ U, rho g v ∈ U) ∧ IsCompl W U := by sorry

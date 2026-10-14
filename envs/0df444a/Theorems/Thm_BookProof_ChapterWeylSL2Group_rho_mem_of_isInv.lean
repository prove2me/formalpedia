-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_rho_mem_of_isInv
-- name    : BookProof.ChapterWeylSL2Group.rho_mem_of_isInv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:36:45.915458+00:00
-- url     : https://prove2.me/theorems/6197cae3-204f-45ff-b97c-8b24711792c7
-- title:
--   `BookProof.ChapterWeylSL2Group.rho_mem_of_isInv` (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : R.IsInv W) : ∀ t : ℂ, (∀ v ∈ W, rho (uPlus t) v ∈ W) ∧ (∀ v ∈ W, rho (uMinus t)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.rho_mem_of_isInv` (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : R.IsInv W) : ∀ t : ℂ, (∀ v ∈ W, rho (uPlus t) v ∈ W) ∧ (∀ v ∈ W, rho (uMinus t) v ∈ W)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.rho_mem_of_isInv`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.rho_mem_of_isInv
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem BookProof.ChapterWeylSL2Group.rho_mem_of_isInv (h : IsExpOfSl2 rho R N) {W : Submodule ℂ V} (hW : R.IsInv W) :
    ∀ t : ℂ, (∀ v ∈ W, rho (uPlus t) v ∈ W) ∧ (∀ v ∈ W, rho (uMinus t) v ∈ W) := by sorry

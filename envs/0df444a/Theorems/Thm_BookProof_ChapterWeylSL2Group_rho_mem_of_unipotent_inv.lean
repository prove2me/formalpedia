-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_rho_mem_of_unipotent_inv
-- name    : BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:37:48.562991+00:00
-- url     : https://prove2.me/theorems/f6e30fe2-86fe-4878-b980-1a373f007131
-- title:
--   `BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv` {W : Submodule ℂ V} (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W) (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv` {W : Submodule ℂ V} (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W) (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W) (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ∀ v ∈ W, rho g v ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv
import Definitions.Def_ChapterWeylSl2
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem BookProof.ChapterWeylSL2Group.rho_mem_of_unipotent_inv {W : Submodule ℂ V}
    (hplus : ∀ (t : ℂ), ∀ v ∈ W, rho (uPlus t) v ∈ W)
    (hminus : ∀ (t : ℂ), ∀ v ∈ W, rho (uMinus t) v ∈ W)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ∀ v ∈ W, rho g v ∈ W := by sorry

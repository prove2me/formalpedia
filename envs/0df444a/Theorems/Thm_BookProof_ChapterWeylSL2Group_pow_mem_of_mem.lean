-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Group_pow_mem_of_mem
-- name    : BookProof.ChapterWeylSL2Group.pow_mem_of_mem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:37:55.874962+00:00
-- url     : https://prove2.me/theorems/5292ada1-b29e-4e35-8977-4a04230a32a3
-- title:
--   `BookProof.ChapterWeylSL2Group.pow_mem_of_mem` {W : Submodule ℂ V} {a : Module.End ℂ V} (ha : ∀ x ∈ W, a x ∈ W) {v : V} (hv : v ∈ W) (k : ℕ) : (a ^ k) v ∈ W
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Group`.
--
--   `BookProof.ChapterWeylSL2Group.pow_mem_of_mem` {W : Submodule ℂ V} {a : Module.End ℂ V} (ha : ∀ x ∈ W, a x ∈ W) {v : V} (hv : v ∈ W) (k : ℕ) : (a ^ k) v ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Group.pow_mem_of_mem`.

-- Generated from ChapterWeylSL2Group.lean — theorem BookProof.ChapterWeylSL2Group.pow_mem_of_mem
import Definitions.Def_ChapterWeylSl2
import Mathlib
import Definitions.Def_ChapterWeylSL2Group
open BookProof.ChapterWeylSL2Group



open BookProof.ChapterWeylSl2

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable {rho : Representation ℂ (Matrix.SpecialLinearGroup (Fin 2) ℂ) V} {R : Sl2Rep V} {N : ℕ}

theorem BookProof.ChapterWeylSL2Group.pow_mem_of_mem {W : Submodule ℂ V} {a : Module.End ℂ V} (ha : ∀ x ∈ W, a x ∈ W)
    {v : V} (hv : v ∈ W) (k : ℕ) : (a ^ k) v ∈ W := by sorry

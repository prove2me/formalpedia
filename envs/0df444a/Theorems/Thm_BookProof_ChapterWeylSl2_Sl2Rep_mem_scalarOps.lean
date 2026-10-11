-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_mem_scalarOps
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:41.951979+00:00
-- url     : https://prove2.me/theorems/5f6a8bd0-a493-4a3f-84b2-27347956bce4
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps` {W : Submodule ℂ V} {f : Module.End ℂ V} : f ∈ scalarOps W ↔ (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps` {W : Submodule ℂ V} {f : Module.End ℂ V} : f ∈ scalarOps W ↔ (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps
import Mathlib
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.mem_scalarOps {W : Submodule ℂ V} {f : Module.End ℂ V} :
    f ∈ scalarOps W ↔ (∀ v : V, f v ∈ W) ∧ ∃ c : ℂ, ∀ w ∈ W, f w = c • w := by sorry

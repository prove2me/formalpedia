-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_pow_succ_apply
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:10.660377+00:00
-- url     : https://prove2.me/theorems/d2d8ec3f-9349-4263-949b-661fa92ae40d
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply` (T : Module.End ℂ V) (k : ℕ) (v : V) : (T ^ (k + 1)) v = T ((T ^ k) v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply` (T : Module.End ℂ V) (k : ℕ) (v : V) : (T ^ (k + 1)) v = T ((T ^ k) v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply
import Mathlib
import Definitions.Def_ChapterWeylSl2
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.pow_succ_apply (T : Module.End ℂ V) (k : ℕ) (v : V) :
    (T ^ (k + 1)) v = T ((T ^ k) v) := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_apply_H_F
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:53:02.089913+00:00
-- url     : https://prove2.me/theorems/3688a4fa-4245-4109-b57d-65f4eb6e6f00
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F` (v : V) : R.H (R.F v) = R.F (R.H v) - 2 • R.F v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F` (v : V) : R.H (R.F v) = R.F (R.H v) - 2 • R.F v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.apply_H_F (v : V) : R.H (R.F v) = R.F (R.H v) - 2 • R.F v := by sorry

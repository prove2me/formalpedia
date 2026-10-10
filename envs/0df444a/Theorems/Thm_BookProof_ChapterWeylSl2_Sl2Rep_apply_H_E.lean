-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_apply_H_E
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:53:03.368424+00:00
-- url     : https://prove2.me/theorems/6ab752a7-912c-412e-abc1-b524ff492817
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E` (v : V) : R.H (R.E v) = R.E (R.H v) + 2 • R.E v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E` (v : V) : R.H (R.E v) = R.E (R.H v) + 2 • R.E v
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.apply_H_E (v : V) : R.H (R.E v) = R.E (R.H v) + 2 • R.E v := by sorry

-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_apply_eq
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:10.502981+00:00
-- url     : https://prove2.me/theorems/53cd37a8-b307-45cd-853e-1205cefa235a
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq` {R : Sl2Rep V} (v : V) : R.cas v = 2 • (R.E (R.F v) + R.F (R.E v)) + R.H (R.H v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq` {R : Sl2Rep V} (v : V) : R.cas v = 2 • (R.E (R.F v) + R.F (R.E v)) + R.H (R.H v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.cas_apply_eq {R : Sl2Rep V} (v : V) :
    R.cas v = 2 • (R.E (R.F v) + R.F (R.E v)) + R.H (R.H v) := by sorry

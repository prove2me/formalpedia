-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_fh_prime
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.fh_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:44.609393+00:00
-- url     : https://prove2.me/theorems/5b3f5546-78b1-49f6-bac2-1d8dcf8a9669
-- title:
--   BookProof.ChapterWeylSl2.Sl2Rep.fh'
-- statement:
--   BookProof.ChapterWeylSl2.Sl2Rep.fh'

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.fh'
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.fh_prime : R.F * R.H - R.H * R.F = 2 • R.F := by sorry

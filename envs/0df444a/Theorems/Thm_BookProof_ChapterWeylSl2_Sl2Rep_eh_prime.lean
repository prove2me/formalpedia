-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_eh_prime
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.eh_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:30.348127+00:00
-- url     : https://prove2.me/theorems/e395645e-4cb8-40d7-8a98-7dc65c047f53
-- title:
--   BookProof.ChapterWeylSl2.Sl2Rep.eh'
-- statement:
--   BookProof.ChapterWeylSl2.Sl2Rep.eh'

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.eh'
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.eh_prime : R.E * R.H - R.H * R.E = -(2 • R.E) := by sorry

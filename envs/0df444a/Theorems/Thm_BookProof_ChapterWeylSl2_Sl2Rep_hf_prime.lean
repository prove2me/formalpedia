-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_hf_prime
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.hf_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:39:07.480571+00:00
-- url     : https://prove2.me/theorems/c628051e-0fb1-4a2e-8090-21fd66899207
-- title:
--   BookProof.ChapterWeylSl2.Sl2Rep.hf'
-- statement:
--   BookProof.ChapterWeylSl2.Sl2Rep.hf'

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.hf'
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.hf_prime : R.H * R.F = R.F * R.H - 2 • R.F := by sorry

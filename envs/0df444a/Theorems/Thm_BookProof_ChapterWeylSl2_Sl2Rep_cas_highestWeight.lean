-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_highestWeight
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:14.342984+00:00
-- url     : https://prove2.me/theorems/20b59956-d193-47a1-98af-3a40708a0b59
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight` {R : Sl2Rep V} {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) : R.cas w = (lam ^ 2 + 2 * lam) • w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight` {R : Sl2Rep V} {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) : R.cas w = (lam ^ 2 + 2 * lam) • w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight {R : Sl2Rep V} {w : V} {lam : ℂ} (hE : R.E w = 0)
    (h : R.H w = lam • w) : R.cas w = (lam ^ 2 + 2 * lam) • w := by sorry

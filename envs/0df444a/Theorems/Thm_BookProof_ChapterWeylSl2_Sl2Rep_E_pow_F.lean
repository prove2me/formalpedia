-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_E_pow_F
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:50:22.181994+00:00
-- url     : https://prove2.me/theorems/f6a8830e-4a70-43b7-a1df-b6a4514faf98
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F` {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) (k : ℕ) : R.E ((R.F ^ (k + 1)) w) = ((k + 1 : ℂ) * (lam - k)) • (R.F ^ k) w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F` {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) (k : ℕ) : R.E ((R.F ^ (k + 1)) w) = ((k + 1 : ℂ) * (lam - k)) • (R.F ^ k) w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.E_pow_F {w : V} {lam : ℂ} (hE : R.E w = 0) (h : R.H w = lam • w) (k : ℕ) :
    R.E ((R.F ^ (k + 1)) w) = ((k + 1 : ℂ) * (lam - k)) • (R.F ^ k) w := by sorry

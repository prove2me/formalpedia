-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_H_pow_F
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:37.136979+00:00
-- url     : https://prove2.me/theorems/1c6f0ae7-dabc-43f5-b5b0-c051b3dca160
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F` {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) : R.H ((R.F ^ k) w) = (lam - 2 * k) • (R.F ^ k) w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F` {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) : R.H ((R.F ^ k) w) = (lam - 2 * k) • (R.F ^ k) w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.H_pow_F {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) :
    R.H ((R.F ^ k) w) = (lam - 2 * k) • (R.F ^ k) w := by sorry

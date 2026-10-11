-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_H_pow_E
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:38:41.035913+00:00
-- url     : https://prove2.me/theorems/86d654b8-8f90-48e5-b869-04574bfe0a74
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E` {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) : R.H ((R.E ^ k) w) = (lam + 2 * k) • (R.E ^ k) w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E` {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) : R.H ((R.E ^ k) w) = (lam + 2 * k) • (R.E ^ k) w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.H_pow_E {w : V} {lam : ℂ} (h : R.H w = lam • w) (k : ℕ) :
    R.H ((R.E ^ k) w) = (lam + 2 * k) • (R.E ^ k) w := by sorry

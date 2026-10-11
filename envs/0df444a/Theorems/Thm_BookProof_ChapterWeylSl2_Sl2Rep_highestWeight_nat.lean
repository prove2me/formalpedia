-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_highestWeight_nat
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:43.371731+00:00
-- url     : https://prove2.me/theorems/8479927b-4ea8-4c4d-adcc-58f1ffee3979
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat` [FiniteDimensional ℂ V] {R : Sl2Rep V} {w : V} {lam : ℂ} (hw : w ≠ 0) (hE : R.E w = 0) (h : R.H w = lam • w) : ∃ m : ℕ, lam = (m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat` [FiniteDimensional ℂ V] {R : Sl2Rep V} {w : V} {lam : ℂ} (hw : w ≠ 0) (hE : R.E w = 0) (h : R.H w = lam • w) : ∃ m : ℕ, lam = (m : ℂ) ∧ (R.F ^ (m + 1)) w = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat [FiniteDimensional ℂ V] {R : Sl2Rep V} {w : V} {lam : ℂ}
    (hw : w ≠ 0) (hE : R.E w = 0) (h : R.H w = lam • w) :
    ∃ m : ℕ, lam = (m : ℂ) ∧ (R.F ^ (m + 1)) w = 0 := by sorry

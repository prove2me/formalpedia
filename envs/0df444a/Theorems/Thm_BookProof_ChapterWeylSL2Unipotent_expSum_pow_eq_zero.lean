-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSL2Unipotent_expSum_pow_eq_zero
-- name    : BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:37:59.424236+00:00
-- url     : https://prove2.me/theorems/7b6c790e-df30-4318-9911-954ab37898fc
-- title:
--   `BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero` {A : Module.End ℂ V} {N m : ℕ} (hnil : A ^ N = 0) (hNm : N ≤ m) : A ^ m = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSL2Unipotent`.
--
--   `BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero` {A : Module.End ℂ V} {N m : ℕ} (hnil : A ^ N = 0) (hNm : N ≤ m) : A ^ m = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero`.

-- Generated from ChapterWeylSL2Unipotent.lean — theorem BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterWeylSL2Group
import Mathlib
import Definitions.Def_ChapterWeylSL2Unipotent
open BookProof.ChapterWeylSL2Unipotent



open BookProof.ChapterWeylSl2 BookProof.ChapterWeylSL2Group
open Polynomial

universe u

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem BookProof.ChapterWeylSL2Unipotent.expSum_pow_eq_zero {A : Module.End ℂ V} {N m : ℕ} (hnil : A ^ N = 0) (hNm : N ≤ m) :
    A ^ m = 0 := by sorry

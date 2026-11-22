-- Prove2me | Theorems.Thm_Egrs75_RoundUp_ru_bounds
-- name    : Egrs75.RoundUp.ru_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:46.339689+00:00
-- url     : https://prove2.me/theorems/2043cdeb-158f-4c4f-85ec-86fb5fbb8926
-- title:
--   Round Up: ru bounds
-- statement:
--   **The EGRS density Fact, as bounds on `ru`.** For odd `p ≥ 3` and `x ≥ 1`:
--   `x ≤ ru p x` and `ru p x < 2*x`. Hence the smallest `LowDigits p` number `≥ x`
--   lies in `[x, 2x)`. KERNEL-CLEAN.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L155-L230
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/RoundUp.lean#L155-L230

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_RoundUp
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RoundUp
open Nat
open Egrs75
variable (p : ℕ)

theorem Egrs75.RoundUp.ru_bounds {p : ℕ} (hp : 3 ≤ p) (hodd : Odd p) :
    ∀ x, 1 ≤ x → x ≤ ru p x ∧ ru p x < 2 * x := by sorry

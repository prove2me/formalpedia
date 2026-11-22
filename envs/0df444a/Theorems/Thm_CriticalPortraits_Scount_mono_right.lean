-- Prove2me | Theorems.Thm_CriticalPortraits_Scount_mono_right
-- name    : CriticalPortraits.Scount_mono_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:51.02742+00:00
-- url     : https://prove2.me/theorems/442c34bc-16a0-4551-bc1e-fec7cf110bb6
-- title:
--   Critical Portraits: Scount mono right
-- statement:
--   Shrinking the upper endpoint shrinks the open interval: `Scount` is monotone in `y`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1044-L1050
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1044-L1050

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.Scount_mono_right {d m : ℕ} (U : Finset (ZMod (d * m))) {x y y' : ℕ}
    (hyy : y ≤ y') : Scount U x y ≤ Scount U x y' := by sorry

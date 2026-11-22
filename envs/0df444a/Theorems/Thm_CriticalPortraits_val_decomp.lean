-- Prove2me | Theorems.Thm_CriticalPortraits_val_decomp
-- name    : CriticalPortraits.val_decomp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:19.536619+00:00
-- url     : https://prove2.me/theorems/49ad2559-f40d-465f-9930-52fdbfc6765d
-- title:
--   Critical Portraits: val decomp
-- statement:
--   `i.val = (i.val % m) + (i.val / m) * m`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L473-L474
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Forward.lean#L473-L474

module
public import Definitions.Def_LeanPool_CriticalPortraits_Core
public import Definitions.Def_LeanPool_CriticalPortraits_Portraits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators

theorem CriticalPortraits.val_decomp {N m : ℕ} (i : ZMod N) : i.val = (i.val % m) + (i.val / m) * m := by sorry

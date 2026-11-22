-- Prove2me | Theorems.Thm_CriticalPortraits_survivorFamily_saturated
-- name    : CriticalPortraits.survivorFamily_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:40.941184+00:00
-- url     : https://prove2.me/theorems/7f1f91ae-dd7b-4fba-b16e-faae763ae881
-- title:
--   Critical Portraits: survivor Family saturated
-- statement:
--   **Geometric saturation.** `N (survivorFamily) 0 (d-1) = d - 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L495-L500
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Injectivity.lean#L495-L500

module
public import Definitions.Def_LeanPool_CriticalPortraits_Forward
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
set_option autoImplicit true
@[expose] public section
public section
open Finset
open scoped BigOperators
open CriticalPortraits
open Finset
open scoped BigOperators
variable {d m : ℕ}

theorem CriticalPortraits.survivorFamily_saturated [NeZero (d * m)] (hd : 0 < d) (hm : 0 < m)
    {P : Finset (Finset (ZMod (d * m)))} (hP : Portrait d m P) :
    AbstractLaminar.N (survivorFamily hd hm hP) 0 (d - 1) = (d - 1) - 0 := by sorry

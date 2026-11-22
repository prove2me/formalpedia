-- Prove2me | Theorems.Thm_CriticalPortraits_T_surjOn
-- name    : CriticalPortraits.T_surjOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:31:31.527184+00:00
-- url     : https://prove2.me/theorems/8f210837-aa10-4208-a250-a8456e1d6dd1
-- title:
--   Critical Portraits: T surj On
-- statement:
--   **Surjectivity.** `T` is surjective onto canonical `(d-1)`-subsets.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1544-L1548
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CriticalPortraits/Surjectivity.lean#L1544-L1548

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

theorem CriticalPortraits.T_surjOn {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    Set.SurjOn (T (N := d*m)) {P | Portrait d m P}
      {U | U.card = d - 1 ∧ LevelCanonical d m U} := by sorry

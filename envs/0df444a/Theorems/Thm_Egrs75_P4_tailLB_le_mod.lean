-- Prove2me | Theorems.Thm_Egrs75_P4_tailLB_le_mod
-- name    : Egrs75.P4.tailLB_le_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:57.220187+00:00
-- url     : https://prove2.me/theorems/0d6f3647-f4ce-4625-92aa-a4adebac5288
-- title:
--   P4: tail LB le mod
-- statement:
--   **Inductive tail bound (KERNEL-CLEAN).**  For `j = topBadIndex q n`, `i = leastGoodAbove`,
--   and any `t` with `j < t ≤ i`: `tailLB q n j t ≤ n % q^t`.  The middle digits being exactly
--   `B` (`middle_digit_eq`) feed the inductive step.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L242-L279
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L242-L279

module
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.GeomSum
public import Definitions.Def_LeanPool_Egrs75_ConditionThreeWindow
set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.P4
open Nat
open Finset
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV

theorem Egrs75.P4.tailLB_le_mod {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n)
    {t : ℕ} (htlo : topBadIndex q n < t) (hthi : t ≤ leastGoodAbove hq hbad) :
    tailLB q n (topBadIndex q n) t ≤ n % q ^ t := by sorry

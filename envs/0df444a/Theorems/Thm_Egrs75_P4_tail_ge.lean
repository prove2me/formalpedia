-- Prove2me | Theorems.Thm_Egrs75_P4_tail_ge
-- name    : Egrs75.P4.tail_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:27:35.61759+00:00
-- url     : https://prove2.me/theorems/b00d4fac-6152-4ebe-b42e-e7338898226b
-- title:
--   P4: tail ge
-- statement:
--   **THE TAIL LOWER BOUND (KERNEL-CLEAN).**  `(q-1)/2 · G q i + 1 ≤ n % q^i`, where
--   `i = leastGoodAbove`.  Assembles `tailLB_le_mod` (at `t = i`) with `b_j ≥ B+1` and the
--   golden identity: `tailLB q n j i = b_j q^j + B(q^{j+1}+…+q^{i-1}) ≥ B·G i + 1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L284-L333
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L284-L333

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

theorem Egrs75.P4.tail_ge {q n : ℕ} (hq : 3 ≤ q) (hbad : 0 < badCountQ q n) :
    (q - 1) / 2 * geomQ q (leastGoodAbove hq hbad) + 1 ≤ n % q ^ (leastGoodAbove hq hbad) := by sorry

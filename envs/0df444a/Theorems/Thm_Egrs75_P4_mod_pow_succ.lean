-- Prove2me | Theorems.Thm_Egrs75_P4_mod_pow_succ
-- name    : Egrs75.P4.mod_pow_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:28:55.984384+00:00
-- url     : https://prove2.me/theorems/c120ca87-721e-4e1d-88b2-506a3858fa60
-- title:
--   P4: mod pow succ
-- statement:
--   Base-`q` mod-recursion (KERNEL-CLEAN): `n % q^{t+1} = n % q^t + q^t·(n / q^t % q)`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L229-L232
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/ConditionThreeWindow.lean#L229-L232

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

theorem Egrs75.P4.mod_pow_succ (n q t : ℕ) :
    n % q ^ (t + 1) = n % q ^ t + q ^ t * (n / q ^ t % q) := by sorry

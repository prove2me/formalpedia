-- Prove2me | Theorems.Thm_Erdos685_choose_le_pow_omega
-- name    : Erdos685.choose_le_pow_omega
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:41:28.962801+00:00
-- url     : https://prove2.me/theorems/2e418bf5-a46f-4c86-a756-56e4f2f55829
-- title:
--   Erdos685: choose le pow omega
-- statement:
--   Every prime-power block of a binomial coefficient is at most its upper index.
--
--   Source: https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Solution.lean#L28-L37
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Solution.lean#L28-L37

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_Erdos685ElementaryLowerBound_Solution
set_option autoImplicit false
@[expose] public section
public section
open Real Finset
open scoped ArithmeticFunction.omega
open Erdos685

theorem Erdos685.choose_le_pow_omega {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    n.choose k ≤ n ^ (ω (n.choose k)) := by sorry

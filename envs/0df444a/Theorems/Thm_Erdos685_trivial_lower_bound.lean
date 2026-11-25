-- Prove2me | Theorems.Thm_Erdos685_trivial_lower_bound
-- name    : Erdos685.trivial_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T12:45:43.375889+00:00
-- url     : https://prove2.me/theorems/ec422520-868d-54c7-abba-61801128eab6
-- title:
--   Erdos685: trivial lower bound
-- statement:
--   The elementary logarithmic lower bound recorded with Erdős problem 685.
--
--   Source: https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Solution.lean#L40-L48
-- source:
--   https://github.com/AItoBit/erdos-685-elementary-lower-bound/blob/c8618095373664c5c8ea35f78304abdd4ec41691/Solution.lean#L40-L48

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

theorem Erdos685.trivial_lower_bound (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    log (n.choose k : ℝ) / log (n : ℝ) ≤ (ω (n.choose k) : ℝ) := by sorry

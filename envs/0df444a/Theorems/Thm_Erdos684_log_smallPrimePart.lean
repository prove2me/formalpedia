-- Prove2me | Theorems.Thm_Erdos684_log_smallPrimePart
-- name    : Erdos684.log_smallPrimePart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:58.241837+00:00
-- url     : https://prove2.me/theorems/820293e4-7aa8-4796-802f-690eb9e1ebf8
-- title:
--   Erdos684: log small Prime Part
-- statement:
--   The logarithm is the weighted sum of small-prime valuations.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L45-L53
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L45-L53

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
set_option autoImplicit false
@[expose] public section
public section
open Erdos684

theorem Erdos684.log_smallPrimePart (n k : ℕ) :
    Real.log (smallPrimePart n k : ℝ) =
      ∑ p ∈ Nat.primesLE k, ((n.choose k).factorization p : ℝ) * Real.log p := by sorry

-- Prove2me | Theorems.Thm_Erdos684_smallPrimePart_pos
-- name    : Erdos684.smallPrimePart_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:19:58.632862+00:00
-- url     : https://prove2.me/theorems/2eff98c5-6ed5-400d-a051-06e097aa9170
-- title:
--   Erdos684: small Prime Part pos
-- statement:
--   The Erdos684 construction uses the small Prime Part pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L39-L42
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Finite.lean#L39-L42

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

theorem Erdos684.smallPrimePart_pos (n k : ℕ) : 0 < smallPrimePart n k := by sorry

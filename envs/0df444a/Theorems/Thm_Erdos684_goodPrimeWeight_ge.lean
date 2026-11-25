-- Prove2me | Theorems.Thm_Erdos684_goodPrimeWeight_ge
-- name    : Erdos684.goodPrimeWeight_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:57.7445+00:00
-- url     : https://prove2.me/theorems/3a9d9591-2a4e-4ca7-a89b-0edf7194d5fc
-- title:
--   Erdos684: good Prime Weight ge
-- statement:
--   The Erdos684 construction uses the good Prime Weight ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L40-L54
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L40-L54

module
public import Definitions.Def_Erdos684_Finite
public import Definitions.Def_Erdos684_BadPrimes
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Definitions.Def_Erdos684_Averaging
set_option autoImplicit false
@[expose] public section
public section
open Finset Real
open Erdos684

theorem Erdos684.goodPrimeWeight_ge (n X A : ℕ) (hn : 0 < n) :
    Chebyshev.theta X - A * log (n + A : ℕ) ≤
      ∑ p ∈ goodPrimes n X A, log p := by sorry

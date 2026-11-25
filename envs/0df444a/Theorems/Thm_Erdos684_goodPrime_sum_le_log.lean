-- Prove2me | Theorems.Thm_Erdos684_goodPrime_sum_le_log
-- name    : Erdos684.goodPrime_sum_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:39:10.721088+00:00
-- url     : https://prove2.me/theorems/397aeac2-5908-4c19-87a4-7a4939136198
-- title:
--   Erdos684: good Prime sum le log
-- statement:
--   The Erdos684 construction uses the good Prime sum le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L100-L114
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L100-L114

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

theorem Erdos684.goodPrime_sum_le_log (n X A k : ℕ) :
    ∑ p ∈ goodPrimes n X A, primeWeight n k p ≤ log (smallPrimePart n k : ℝ) := by sorry

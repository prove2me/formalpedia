-- Prove2me | Theorems.Thm_Erdos684_goodPrime_window_weight
-- name    : Erdos684.goodPrime_window_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:30:00.001452+00:00
-- url     : https://prove2.me/theorems/6166b0fb-2d75-4530-a703-cbc48621fc2f
-- title:
--   Erdos684: good Prime window weight
-- statement:
--   The Erdos684 construction uses the good Prime window weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L56-L98
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L56-L98

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

theorem Erdos684.goodPrime_window_weight {n X A p : ℕ} (hX : 2 * X ≤ n)
    (hp : p ∈ goodPrimes n X A) :
    (A : ℝ) * log p ≤ ∑ k ∈ Finset.Icc 1 (2 * X), primeWeight n k p := by sorry

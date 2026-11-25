-- Prove2me | Theorems.Thm_Erdos684_frequently_smallPrimePart_eq_one
-- name    : Erdos684.frequently_smallPrimePart_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T16:03:09.902411+00:00
-- url     : https://prove2.me/theorems/07bbb4bb-acee-4d0b-9988-73e08392a15e
-- title:
--   Erdos684: frequently small Prime Part eq one
-- statement:
--   Infinitely many inputs have small-prime part one throughout a logarithmic window.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Lower.lean#L72-L94
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Lower.lean#L72-L94

module
public import Definitions.Def_Erdos684_Finite
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Erdos684_Lower
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos684

theorem Erdos684.frequently_smallPrimePart_eq_one :
    ∃ᶠ n : ℕ in atTop, 1 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ log (n : ℝ) / 8 → smallPrimePart n k = 1 := by sorry

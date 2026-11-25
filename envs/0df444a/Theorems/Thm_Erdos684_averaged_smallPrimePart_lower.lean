-- Prove2me | Theorems.Thm_Erdos684_averaged_smallPrimePart_lower
-- name    : Erdos684.averaged_smallPrimePart_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:39:30.437916+00:00
-- url     : https://prove2.me/theorems/91558821-4b3b-4b85-a57d-52ae2a73104c
-- title:
--   Erdos684: averaged small Prime Part lower
-- statement:
--   A finite lower bound on the average small-prime logarithm.
--
--   Source: https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L117-L129
-- source:
--   https://github.com/AItoBit/erdos-684-elementary-bounds/blob/a59cf65171b19dc7785b767d3b88ad8ef754f3eb/Erdos684/Averaging.lean#L117-L129

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

theorem Erdos684.averaged_smallPrimePart_lower (n X A : ℕ) (hn : 0 < n) (hX : 2 * X ≤ n) :
    (A : ℝ) * (Chebyshev.theta X - A * log (n + A : ℕ)) ≤
      ∑ k ∈ Finset.Icc 1 (2 * X), log (smallPrimePart n k : ℝ) := by sorry

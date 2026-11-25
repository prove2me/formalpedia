-- Prove2me | Theorems.Thm_Erdos679_cardDistinctFactors_le_of_dvd
-- name    : Erdos679.cardDistinctFactors_le_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:01:14.756217+00:00
-- url     : https://prove2.me/theorems/8ff2b939-8364-56e8-b813-83b3393b9309
-- title:
--   Erdos679: card Distinct Factors le of dvd
-- statement:
--   Divisibility preserves the number of distinct prime factors when the target is nonzero.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L32-L36
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/CRT.lean#L32-L36

module
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_CRT
set_option autoImplicit false
@[expose] public section
public section
open Erdos679

theorem Erdos679.cardDistinctFactors_le_of_dvd {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    ArithmeticFunction.cardDistinctFactors a ≤ ArithmeticFunction.cardDistinctFactors b := by sorry

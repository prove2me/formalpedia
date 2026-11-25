-- Prove2me | Theorems.Thm_Erdos679_log_factorial_le_stirling
-- name    : Erdos679.log_factorial_le_stirling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:01:14.524447+00:00
-- url     : https://prove2.me/theorems/ff0bf872-25e9-42a6-b15a-31b375df2d91
-- title:
--   Erdos679: log factorial le stirling
-- statement:
--   An elementary upper bound obtained from the decreasing Stirling sequence.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/StirlingBound.lean#L32-L44
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/StirlingBound.lean#L32-L44

module
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos679_StirlingBound
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679

theorem Erdos679.log_factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    log (n.factorial : ℝ) ≤ (n : ℝ) * log n - n + 1 + log n / 2 := by sorry

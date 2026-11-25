-- Prove2me | Theorems.Thm_Erdos679_eventually_log_factorial_le
-- name    : Erdos679.eventually_log_factorial_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:01:14.295947+00:00
-- url     : https://prove2.me/theorems/b92a7929-9f1e-4bc4-912c-a62f347af44a
-- title:
--   Erdos679: eventually log factorial le
-- statement:
--   For sufficiently large natural numbers the linear saving can be chosen as $0.9n$.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/StirlingBound.lean#L47-L66
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Erdos679/StirlingBound.lean#L47-L66

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

theorem Erdos679.eventually_log_factorial_le :
    ∀ᶠ n : ℕ in atTop,
      log (n.factorial : ℝ) ≤ (n : ℝ) * log n - (9 / 10 : ℝ) * n := by sorry

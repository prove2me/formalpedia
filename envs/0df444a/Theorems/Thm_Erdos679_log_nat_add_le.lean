-- Prove2me | Theorems.Thm_Erdos679_log_nat_add_le
-- name    : Erdos679.log_nat_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:21.315522+00:00
-- url     : https://prove2.me/theorems/f9213d8a-39d1-5311-9553-950923421563
-- title:
--   Erdos679: log nat add le
-- statement:
--   Adding a fixed natural number changes the logarithm of a positive integer by at most that number.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L27-L39
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L27-L39

module
public import Definitions.Def_Erdos679_Analytic
public import Definitions.Def_Erdos679_Gap
public import Definitions.Def_Erdos679_CRT
public import Definitions.Def_Erdos679AdditiveRefutation_Solution
set_option autoImplicit false
@[expose] public section
public section
open Filter Real
open scoped Topology
open Erdos679

theorem Erdos679.log_nat_add_le (P K : ℕ) (hP : 0 < P) :
    log ((P + K : ℕ) : ℝ) ≤ log (P : ℝ) + K := by sorry

-- Prove2me | Theorems.Thm_Erdos679_eventually_shifted_log_primeProduct_gt
-- name    : Erdos679.eventually_shifted_log_primeProduct_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:29:52.943475+00:00
-- url     : https://prove2.me/theorems/74b74207-5793-4c5d-adf0-4e17a5e5cc99
-- title:
--   Erdos679: eventually shifted log prime Product gt
-- statement:
--   The lower primorial estimate also holds after a fixed nonnegative shift.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L56-L61
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L56-L61

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

theorem Erdos679.eventually_shifted_log_primeProduct_gt (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, m * (log m - 2) < log ((primeProduct m + K : ℕ) : ℝ) := by sorry

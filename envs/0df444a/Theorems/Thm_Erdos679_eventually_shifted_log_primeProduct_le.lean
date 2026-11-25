-- Prove2me | Theorems.Thm_Erdos679_eventually_shifted_log_primeProduct_le
-- name    : Erdos679.eventually_shifted_log_primeProduct_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T15:20:30.679874+00:00
-- url     : https://prove2.me/theorems/3f194796-0f73-55db-bd00-a2ef38418288
-- title:
--   Erdos679: eventually shifted log prime Product le
-- statement:
--   A fixed shift preserves a positive linear saving in the primorial logarithm.
--
--   Source: https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L42-L53
-- source:
--   https://github.com/AItoBit/erdos-679-additive-refutation/blob/4a53d358d1b7ade35d6f696f501c99b4d88c9e4c/Solution.lean#L42-L53

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

theorem Erdos679.eventually_shifted_log_primeProduct_le (K : ℕ) :
    ∀ᶠ m : ℕ in atTop, log ((primeProduct m + K : ℕ) : ℝ) ≤
      m * (log m + log (log m) - (1 / 5 : ℝ)) := by sorry

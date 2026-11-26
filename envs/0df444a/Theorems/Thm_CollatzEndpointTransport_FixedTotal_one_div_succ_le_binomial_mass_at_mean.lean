-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_div_succ_le_binomial_mass_at_mean
-- name    : CollatzEndpointTransport.FixedTotal.one_div_succ_le_binomial_mass_at_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:24.829628+00:00
-- url     : https://prove2.me/theorems/634591f5-4581-4c75-9c3a-32602b49ce0b
-- title:
--   Fixed Total: one div succ le binomial mass at mean
-- statement:
--   Real-valued probability form used in the terminal-pattern comparison.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L812-L841
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L812-L841

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.one_div_succ_le_binomial_mass_at_mean
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (1 : ℝ) / (n + 1) ≤
      (n.choose k : ℝ) *
        ((k : ℝ) / n) ^ k *
        (((n - k : ℕ) : ℝ) / n) ^ (n - k) := by sorry

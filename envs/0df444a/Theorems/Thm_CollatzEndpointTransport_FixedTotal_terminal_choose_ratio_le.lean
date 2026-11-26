-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminal_choose_ratio_le
-- name    : CollatzEndpointTransport.FixedTotal.terminal_choose_ratio_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:54.535945+00:00
-- url     : https://prove2.me/theorems/bf20061e-13c8-5a28-a46b-6f6876a1b489
-- title:
--   Fixed Total: terminal choose ratio le
-- statement:
--   Conditional terminal-pattern comparison in pure binomial form.
--
--   Here `n = N-1`, `k = s-1`, `r` separator positions and `D-r`
--   nonseparator positions have been prescribed.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L871-L939
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L871-L939

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

theorem CollatzEndpointTransport.FixedTotal.terminal_choose_ratio_le
    {n k D r : ℕ}
    (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    (hrk : r ≤ k) (hrD : r ≤ D)
    (hDr : D - r ≤ n - k) :
    ((n - D).choose (k - r) : ℝ) / (n.choose k : ℝ) ≤
      (n + 1 : ℝ) *
        ((k : ℝ) / n) ^ r *
        (((n - k : ℕ) : ℝ) / n) ^ (D - r) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_descFactorial_div_descFactorial_le_pow_div
-- name    : CollatzEndpointTransport.FixedTotal.descFactorial_div_descFactorial_le_pow_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:13.777053+00:00
-- url     : https://prove2.me/theorems/2f607a3e-e9ce-516c-a421-fb45d7ef8161
-- title:
--   Fixed Total: desc Factorial div desc Factorial le pow div
-- statement:
--   A falling-factorial ratio for sampling without replacement is bounded by
--   the corresponding power for independent sampling.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L32-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L32-L64

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
variable {α : Type*} [DecidableEq α]

theorem CollatzEndpointTransport.FixedTotal.descFactorial_div_descFactorial_le_pow_div
    {n k j : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hjk : j ≤ k) :
    ((k.descFactorial j : ℕ) : ℝ) /
        ((n.descFactorial j : ℕ) : ℝ) ≤
      ((k : ℝ) / n) ^ j := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_choose_sub_div_choose_le_pow_div
-- name    : CollatzEndpointTransport.FixedTotal.choose_sub_div_choose_le_pow_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:51.110261+00:00
-- url     : https://prove2.me/theorems/efb176c4-0ff3-4d51-a7d9-c9173bf8f633
-- title:
--   Fixed Total: choose sub div choose le pow div
-- statement:
--   The probability that a uniform subset of size k in a set of size n
--   contains j prescribed points is at most the corresponding independent
--   probability.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L69-L101
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L69-L101

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

theorem CollatzEndpointTransport.FixedTotal.choose_sub_div_choose_le_pow_div
    {n k j : ℕ} (hn : 0 < n) (hkn : k ≤ n) (hjk : j ≤ k) :
    (((n - j).choose (k - j) : ℕ) : ℝ) / (n.choose k : ℕ) ≤
      ((k : ℝ) / n) ^ j := by sorry

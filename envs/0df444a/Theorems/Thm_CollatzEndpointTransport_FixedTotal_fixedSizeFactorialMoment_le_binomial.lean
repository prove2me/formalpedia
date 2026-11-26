-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeFactorialMoment_le_binomial
-- name    : CollatzEndpointTransport.FixedTotal.fixedSizeFactorialMoment_le_binomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:54.371633+00:00
-- url     : https://prove2.me/theorems/2bc9047b-99f7-40c8-a46e-56ad50f9e770
-- title:
--   Fixed Total: fixed Size Factorial Moment le binomial
-- statement:
--   The factorial-moment expansion for a fixed-size sample is bounded by
--   the binomial moment with the same one-point marginal.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L105-L145
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L105-L145

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

theorem CollatzEndpointTransport.FixedTotal.fixedSizeFactorialMoment_le_binomial
    {n k m : ℕ} {t : ℝ}
    (hn : 0 < n) (hkn : k ≤ n) (ht : 0 ≤ t) :
    (∑ j ∈ range (m + 1),
        if hjk : j ≤ k then
          (m.choose j : ℝ) *
            (((n - j).choose (k - j) : ℕ) : ℝ) /
              (n.choose k : ℕ) * t ^ j
        else 0) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by sorry

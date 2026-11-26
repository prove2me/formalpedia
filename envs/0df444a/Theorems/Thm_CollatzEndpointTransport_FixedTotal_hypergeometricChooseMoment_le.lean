-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_hypergeometricChooseMoment_le
-- name    : CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:46.25802+00:00
-- url     : https://prove2.me/theorems/055316d0-f8a1-5a60-b659-4d8abbeee9a3
-- title:
--   Fixed Total: hypergeometric Choose Moment le
-- statement:
--   Cardinal form of the fixed-size hypergeometric moment bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L443-L459
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L443-L459

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

theorem CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_le
    {n k m : ℕ} {t : ℝ}
    (hmn : m ≤ n) (hkn : k ≤ n) (hn : 0 < n) (ht : 0 ≤ t) :
    (∑ j ∈ range (m + 1),
        if _hjk : j ≤ k then
          (m.choose j : ℝ) * ((n - m).choose (k - j) : ℝ) *
            (1 + t) ^ j
        else 0) / (n.choose k : ℝ) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by sorry

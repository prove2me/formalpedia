-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_hypergeometricChooseMoment_ambient_le
-- name    : CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_ambient_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:39:49.019808+00:00
-- url     : https://prove2.me/theorems/0758dc2d-a878-48d0-800e-e2c0ff8b11d2
-- title:
--   Fixed Total: hypergeometric Choose Moment ambient le
-- statement:
--   The same cardinal bound on the full ambient range; the additional terms
--   vanish because their marked-set binomial coefficient is zero.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L463-L489
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L463-L489

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

theorem CollatzEndpointTransport.FixedTotal.hypergeometricChooseMoment_ambient_le
    {n k m : ℕ} {t : ℝ}
    (hmn : m ≤ n) (hkn : k ≤ n) (hn : 0 < n) (ht : 0 ≤ t) :
    (∑ j ∈ range (n + 1),
        if _hjk : j ≤ k then
          (m.choose j : ℝ) * ((n - m).choose (k - j) : ℝ) *
            (1 + t) ^ j
        else 0) / (n.choose k : ℝ) ≤
      (1 + ((k : ℝ) / n) * t) ^ m := by sorry

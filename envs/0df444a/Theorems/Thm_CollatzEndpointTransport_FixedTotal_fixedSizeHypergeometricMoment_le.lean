-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeHypergeometricMoment_le
-- name    : CollatzEndpointTransport.FixedTotal.fixedSizeHypergeometricMoment_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:39:21.755862+00:00
-- url     : https://prove2.me/theorems/2e420a61-1201-4df4-b100-92fd4dd63676
-- title:
--   Fixed Total: fixed Size Hypergeometric Moment le
-- statement:
--   Numerical hypergeometric moment bound, obtained by grouping the generic
--   fixed-size subset moment according to the marked intersection size.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L356-L440
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L356-L440

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

theorem CollatzEndpointTransport.FixedTotal.fixedSizeHypergeometricMoment_le
    (V U : Finset α) {k : ℕ} {t : ℝ}
    (hUV : U ⊆ V) (hkV : k ≤ V.card) (hV : V.Nonempty)
    (ht : 0 ≤ t) :
    (∑ j ∈ range (U.card + 1),
        if hjk : j ≤ k then
          (U.card.choose j : ℝ) *
            ((V.card - U.card).choose (k - j) : ℝ) *
              (1 + t) ^ j
        else 0) / (V.card.choose k : ℝ) ≤
      (1 + ((k : ℝ) / V.card) * t) ^ U.card := by sorry

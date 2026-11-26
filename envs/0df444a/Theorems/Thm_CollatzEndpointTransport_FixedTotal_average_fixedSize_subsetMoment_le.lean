-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_average_fixedSize_subsetMoment_le
-- name    : CollatzEndpointTransport.FixedTotal.average_fixedSize_subsetMoment_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:17.683886+00:00
-- url     : https://prove2.me/theorems/a1c9868d-0271-4361-8113-f64ee382788c
-- title:
--   Fixed Total: average fixed Size subset Moment le
-- statement:
--   Moment domination for sampling a fixed-size subset. The marked-count
--   moment is no larger than for independent selectors with the same one-point
--   marginal.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L179-L247
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean#L179-L247

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

theorem CollatzEndpointTransport.FixedTotal.average_fixedSize_subsetMoment_le
    (V U : Finset α) {k : ℕ} {t : ℝ}
    (hUV : U ⊆ V) (hkV : k ≤ V.card) (hV : V.Nonempty)
    (ht : 0 ≤ t) :
    (∑ S ∈ V.powersetCard k, (1 + t) ^ (U ∩ S).card) /
        (V.card.choose k : ℝ) ≤
      (1 + ((k : ℝ) / V.card) * t) ^ U.card := by sorry

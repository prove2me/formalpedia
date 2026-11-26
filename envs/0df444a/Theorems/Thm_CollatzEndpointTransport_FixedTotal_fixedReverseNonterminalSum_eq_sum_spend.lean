-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseNonterminalSum_eq_sum_spend
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_eq_sum_spend
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:40:39.295801+00:00
-- url     : https://prove2.me/theorems/101fa912-c5c1-451c-90f2-0f8f060c820a
-- title:
--   Fixed Total: fixed Reverse Nonterminal Sum eq sum spend
-- statement:
--   Reordering first by terminal-block length and then by terminal spend.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L246-L266
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L246-L266

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_eq_sum_spend
    (N s : ℕ) (theta : ℝ) :
    fixedReverseNonterminalSum N s theta =
      ∑ D ∈ range (N + 1), fixedReverseSpendSum N s theta D := by sorry

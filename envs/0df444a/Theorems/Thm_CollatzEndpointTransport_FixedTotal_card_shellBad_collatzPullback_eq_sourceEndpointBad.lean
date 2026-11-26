-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_shellBad_collatzPullback_eq_sourceEndpointBad
-- name    : CollatzEndpointTransport.FixedTotal.card_shellBad_collatzPullback_eq_sourceEndpointBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:25.665417+00:00
-- url     : https://prove2.me/theorems/37514bd0-f116-523d-8e5b-a19c41be0103
-- title:
--   Fixed Total: card shell Bad collatz Pullback eq source Endpoint Bad
-- statement:
--   Exact cardinal bridge from source-code endpoint failures to the actual
--   one-block Collatz pullback complement.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L161-L167
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L161-L167

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_shellBad_collatzPullback_eq_sourceEndpointBad
    (S : Set ℕ) (M : ℕ) :
    (QuantitativeDensity.shellBad
        (QuantitativeDensity.collatzPullback S) M).card =
      (sourceEndpointBad S M).card := by sorry

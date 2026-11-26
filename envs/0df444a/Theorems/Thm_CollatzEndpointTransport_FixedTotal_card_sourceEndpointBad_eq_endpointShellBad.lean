-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_eq_endpointShellBad
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_endpointShellBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:09.061199+00:00
-- url     : https://prove2.me/theorems/2c540a3c-1b08-4e6e-8681-b1c4ebe2355c
-- title:
--   Fixed Total: card source Endpoint Bad eq endpoint Shell Bad
-- statement:
--   The Fixed Total construction uses the card source Endpoint Bad eq endpoint Shell Bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L86-L132
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalShellCoding.lean#L86-L132

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalGlobalEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_eq_endpointShellBad
    (S : Set ℕ) (M : ℕ) :
    (sourceEndpointBad S M).card = (endpointShellBad S M).card := by sorry

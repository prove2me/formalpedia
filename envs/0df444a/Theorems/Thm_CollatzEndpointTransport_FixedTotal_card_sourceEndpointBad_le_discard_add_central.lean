-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_le_discard_add_central
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_le_discard_add_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:08:56.180802+00:00
-- url     : https://prove2.me/theorems/284288fd-c5e3-48d1-b745-9ee874cb06f4
-- title:
--   Fixed Total: card source Endpoint Bad le discard add central
-- statement:
--   The Fixed Total construction uses the card source Endpoint Bad le discard add central property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L469-L482
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L469-L482

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq

theorem CollatzEndpointTransport.FixedTotal.card_sourceEndpointBad_le_discard_add_central
    (S : Set ℕ) (M : ℕ) (theta eta : ℝ) :
    (sourceEndpointBad S M).card ≤
      (centralDiscardedSourceSet M theta eta).card +
        (centralSourceEndpointBad S M theta eta).card := by sorry

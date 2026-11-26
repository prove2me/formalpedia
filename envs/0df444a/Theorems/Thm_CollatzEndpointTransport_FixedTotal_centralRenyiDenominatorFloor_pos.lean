-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiDenominatorFloor_pos
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiDenominatorFloor_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:10:15.48531+00:00
-- url     : https://prove2.me/theorems/c916391d-db24-56bb-aae6-fd84aa8203cc
-- title:
--   Fixed Total: central Renyi Denominator Floor pos
-- statement:
--   The Fixed Total construction uses the central Renyi Denominator Floor pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1808-L1830
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1808-L1830

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiDenominatorFloor_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < centralRenyiDenominatorFloor eta := by sorry

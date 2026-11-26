-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiThreshold_mul_oddRate
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_mul_oddRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:05.061825+00:00
-- url     : https://prove2.me/theorems/ef031501-2927-47c0-be39-8a0a98e0b222
-- title:
--   Fixed Total: central Renyi Threshold mul odd Rate
-- statement:
--   The Fixed Total construction uses the central Renyi Threshold mul odd Rate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1078-L1089
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1078-L1089

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_mul_oddRate
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    centralRenyiThreshold theta D M *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M =
      Real.exp (-centralRenyiRate theta D * M) := by sorry

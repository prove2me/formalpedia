-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiThreshold_neg_rpow
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_neg_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:09:58.699779+00:00
-- url     : https://prove2.me/theorems/47aed723-0eb1-59be-bd13-e85e76dafd2a
-- title:
--   Fixed Total: central Renyi Threshold neg rpow
-- statement:
--   The Fixed Total construction uses the central Renyi Threshold neg rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1068-L1076
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1068-L1076

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiThreshold_neg_rpow
    {theta D : ℝ} (M : ℕ) (htheta : 0 < theta) :
    (centralRenyiThreshold theta D M) ^ (-theta) =
      Real.exp (-centralRenyiRate theta D * M) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRate_inv_le
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiRate_inv_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:23.912901+00:00
-- url     : https://prove2.me/theorems/c084c666-4a2b-469c-b302-a4c6b76a5a0a
-- title:
--   Fixed Total: central Renyi Rate inv le
-- statement:
--   The Fixed Total construction uses the central Renyi Rate inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1618-L1653
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1618-L1653

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiRate_inv_le
    {theta transport D : ℝ}
    (htheta0 : 0 < theta)
    (htransport0 : 0 < transport)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    (centralRenyiRate theta D)⁻¹ ≤
      (centralRenyiAbsorption theta transport /
        (transport * Real.log 2)) * D⁻¹ := by sorry

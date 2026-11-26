-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiMomentInverse_le
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiMomentInverse_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:05.894053+00:00
-- url     : https://prove2.me/theorems/6025e8f4-caea-5ce9-9aee-39dd06dd4238
-- title:
--   Fixed Total: central Renyi Moment Inverse le
-- statement:
--   The Fixed Total construction uses the central Renyi Moment Inverse le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1655-L1694
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1655-L1694

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiMomentInverse_le
    {theta transport D : ℝ}
    (htheta0 : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hD0 : 0 < D)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2) :
    ((((1 - centralRenyiAbsorption theta transport) *
      centralRenyiRate theta D / 6)⁻¹) ^ 6) ≤
      centralRenyiInverseRateFactor theta transport * (D⁻¹) ^ 6 := by sorry

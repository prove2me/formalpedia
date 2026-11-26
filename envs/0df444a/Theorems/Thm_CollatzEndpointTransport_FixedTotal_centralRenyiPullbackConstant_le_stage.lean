-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiPullbackConstant_le_stage
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyiPullbackConstant_le_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:46.803586+00:00
-- url     : https://prove2.me/theorems/1dc47c96-c34e-56cd-893f-490f99ce69ea
-- title:
--   Fixed Total: central Renyi Pullback Constant le stage
-- statement:
--   Uniform inverse-sixth-power majorant for the exact central pullback
--   constant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1854-L1937
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1854-L1937

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyiPullbackConstant_le_stage
    {C D theta eta transport : ℝ}
    (hC : 0 < C) (hD0 : 0 < D) (hD1 : D ≤ 1)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hlinear : transport * D ≤
      centralRenyiShellRate theta transport D / Real.log 2)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    centralRenyiPullbackConstant C theta eta transport D ≤
      centralRenyiStageConstant theta eta transport *
        (C + 1) * (D⁻¹) ^ 6 := by sorry

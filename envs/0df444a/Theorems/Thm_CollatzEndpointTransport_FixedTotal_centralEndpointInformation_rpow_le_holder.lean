-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_rpow_le_holder
-- name    : CollatzEndpointTransport.FixedTotal.centralEndpointInformation_rpow_le_holder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:12.957471+00:00
-- url     : https://prove2.me/theorems/09d377fa-7ccd-5239-a7d3-2022c3465355
-- title:
--   Fixed Total: central Endpoint Information rpow le holder
-- statement:
--   Taking the Holder root turns `(M + 1)^(theta / 2)` information into the
--   polynomial factor with exponent `theta / (2 * (1 + theta))`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L49-L94
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L49-L94

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralEndpointInformation_rpow_le_holder
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    (centralEndpointInformation M theta eta) ^ (1 / (1 + theta)) ≤
      holderCentralMomentConstant theta eta *
        (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) := by sorry

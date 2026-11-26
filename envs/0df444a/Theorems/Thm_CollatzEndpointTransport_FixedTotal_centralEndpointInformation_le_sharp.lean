-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralEndpointInformation_le_sharp
-- name    : CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le_sharp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:40.876434+00:00
-- url     : https://prove2.me/theorems/1f7b9868-f625-4c8f-9b76-98ea3b04eeaf
-- title:
--   Fixed Total: central Endpoint Information le sharp
-- statement:
--   Sharp central endpoint information in literal shell coordinates.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L814-L914
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L814-L914

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le_sharp
    {M : ℕ} {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    centralEndpointInformation M theta eta ≤
      2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
        (M + 1 : ℝ) ^ (1 + theta) := by sorry

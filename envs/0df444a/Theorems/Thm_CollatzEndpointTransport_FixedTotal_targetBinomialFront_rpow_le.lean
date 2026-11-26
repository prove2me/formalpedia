-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_targetBinomialFront_rpow_le
-- name    : CollatzEndpointTransport.FixedTotal.targetBinomialFront_rpow_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:24:36.005796+00:00
-- url     : https://prove2.me/theorems/7a23c438-05f4-5d53-905e-553eba4e1d7f
-- title:
--   Fixed Total: target Binomial Front rpow le
-- statement:
--   The target coefficient in the direct Holder estimate is at most the
--   Holder power of `C`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L130-L142
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean#L130-L142

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.targetBinomialFront_rpow_le
    {C D theta : ℝ}
    (hC : 0 < C) (hD : 0 < D) (htheta : 0 < theta) :
    (C * Real.exp (-D * Real.log 3)) ^ holderTargetExponent theta ≤
      C ^ holderTargetExponent theta := by sorry

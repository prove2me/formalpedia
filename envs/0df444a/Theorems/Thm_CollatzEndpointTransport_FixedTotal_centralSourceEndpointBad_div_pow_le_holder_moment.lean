-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le_holder_moment
-- name    : CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_holder_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:45.0663+00:00
-- url     : https://prove2.me/theorems/9c062ca7-75f6-4ff4-a873-7231d2fd8fe4
-- title:
--   Fixed Total: central Source Endpoint Bad div pow le holder moment
-- statement:
--   Direct Holder shell estimate after inserting the existing central moment.
--   The target-density constant appears with the sublinear Holder exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L117-L161
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L117-L161

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_holder_moment
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 : ℝ) ^ M ≤
      (C * Real.exp (-D * Real.log 3)) ^
          (theta / (1 + theta)) *
        holderCentralMomentConstant theta eta *
        (M + 1 : ℝ) ^ (theta / (2 * (1 + theta))) *
        Real.exp (-centralRenyiRate theta D * M) := by sorry

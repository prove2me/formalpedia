-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_targetBinomialFactor_rpow_eq
-- name    : CollatzEndpointTransport.FixedTotal.targetBinomialFactor_rpow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:24:02.620137+00:00
-- url     : https://prove2.me/theorems/3bfbb1d0-d315-5c1c-98be-fae0cea74c4a
-- title:
--   Fixed Total: target Binomial Factor rpow eq
-- statement:
--   The exact target factor raised to the Holder power has exponential rate
--   `centralRenyiRate`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L98-L113
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean#L98-L113

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.targetBinomialFactor_rpow_eq
    {C D theta : ℝ} (M : ℕ)
    (hC : 0 < C) (htheta : 0 < theta) :
    (C * Real.exp (-D * Real.log 3) *
        ((1 + Real.exp (-D * Real.log 3)) / 2) ^ M) ^
          (theta / (1 + theta)) =
      (C * Real.exp (-D * Real.log 3)) ^ (theta / (1 + theta)) *
        Real.exp (-centralRenyiRate theta D * M) := by sorry

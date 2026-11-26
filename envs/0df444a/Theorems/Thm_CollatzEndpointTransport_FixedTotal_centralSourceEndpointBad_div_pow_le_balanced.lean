-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le_balanced
-- name    : CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_balanced
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:19:43.157485+00:00
-- url     : https://prove2.me/theorems/0c417ecc-6667-4511-963e-4b225f030e82
-- title:
--   Fixed Total: central Source Endpoint Bad div pow le balanced
-- statement:
--   Balanced retained-central shell estimate.  The polynomial factor is
--   explicit and does not alter the exponential rate.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1093-L1141
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1093-L1141

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

theorem CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_balanced
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ 6) *
        Real.exp (-centralRenyiRate theta D * M) := by sorry

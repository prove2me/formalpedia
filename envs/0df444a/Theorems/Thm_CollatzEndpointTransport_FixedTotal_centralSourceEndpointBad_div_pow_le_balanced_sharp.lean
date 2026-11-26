-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le_balanced_sharp
-- name    : CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_balanced_sharp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:22:26.474198+00:00
-- url     : https://prove2.me/theorems/30f9a7e3-9c29-4f47-bd1a-87bde1ed5ccb
-- title:
--   Fixed Total: central Source Endpoint Bad div pow le balanced sharp
-- statement:
--   Balanced retained-central shell estimate with the sharp real
--   polynomial exponent.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L975-L1019
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L975-L1019

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

theorem CollatzEndpointTransport.FixedTotal.centralSourceEndpointBad_div_pow_le_balanced_sharp
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) :
    ((centralSourceEndpointBad S M theta eta).card : ℝ) /
        (2 ^ M : ℝ) ≤
      (C * Real.exp (-D * Real.log 3) +
          2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
            (M + 1 : ℝ) ^ (1 + theta)) *
        Real.exp (-centralRenyiRate theta D * M) := by sorry

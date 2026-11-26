-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_startup
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_startup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:18:19.81281+00:00
-- url     : https://prove2.me/theorems/cba1d165-5b05-536b-9504-6dd174459068
-- title:
--   Fixed Total: source Endpoint Bad div pow le central Renyi startup
-- statement:
--   The full finite-shell theorem with all startup conditions discharged by
--   the explicit central startup scale.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1209-L1235
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1209-L1235

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

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_startup
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      ((((M + 1) *
          2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ)) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ 6) *
          Real.exp (-centralRenyiRate theta D * M) := by sorry

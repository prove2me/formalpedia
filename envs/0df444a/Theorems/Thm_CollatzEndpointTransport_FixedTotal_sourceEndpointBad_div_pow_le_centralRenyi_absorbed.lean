-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_absorbed
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:42.715491+00:00
-- url     : https://prove2.me/theorems/bedb38db-7e19-5b75-9050-b18c611a0163
-- title:
--   Fixed Total: source Endpoint Bad div pow le central Renyi absorbed
-- statement:
--   Uniform absorbed central-Renyi shell estimate, including every finite
--   startup shell.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1466-L1545
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1466-L1545

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

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8)
    (M : ℕ) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      centralRenyiShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by sorry

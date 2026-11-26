-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
-- name    : CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:18:53.43404+00:00
-- url     : https://prove2.me/theorems/76c795f9-035b-4852-8d75-311dd2902cbd
-- title:
--   Fixed Total: source Endpoint Bad div pow le central Renyi absorbed large
-- statement:
--   Absorbed central-Renyi shell estimate above the explicit startup scale.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1247-L1395
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1247-L1395

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

theorem CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_absorbed_large
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
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      centralRenyiLargeShellConstant C theta eta transport D *
        Real.exp (-centralRenyiShellRate theta transport D * M) := by sorry

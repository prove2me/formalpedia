-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_collatzPullback_dense_centralRenyi
-- name    : CollatzEndpointTransport.FixedTotal.collatzPullback_dense_centralRenyi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:42:26.08329+00:00
-- url     : https://prove2.me/theorems/e4a82545-21f0-4a80-9299-7e8effe06e55
-- title:
--   Fixed Total: collatz Pullback dense central Renyi
-- statement:
--   Concrete central higher-Renyi Collatz pullback in `(C,D)`-density form.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1577-L1601
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L1577-L1601

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

theorem CollatzEndpointTransport.FixedTotal.collatzPullback_dense_centralRenyi
    {S : Set ℕ} {C D theta eta transport : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta)
    (hcutLate : centralRenyiShellRate theta transport D ≤
      eta * Real.log 2 / 16)
    (hcutParity : centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8) :
    QuantitativeDensity.IsCDDense
      (QuantitativeDensity.collatzPullback S)
      (centralRenyiPullbackConstant C theta eta transport D)
      (centralRenyiShellRate theta transport D / Real.log 2) := by sorry

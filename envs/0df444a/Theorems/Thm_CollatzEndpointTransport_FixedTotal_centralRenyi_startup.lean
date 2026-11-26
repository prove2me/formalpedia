-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_startup
-- name    : CollatzEndpointTransport.FixedTotal.centralRenyi_startup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:07:37.909981+00:00
-- url     : https://prove2.me/theorems/d4b4b961-1d76-4957-af85-09655966f29d
-- title:
--   Fixed Total: central Renyi startup
-- statement:
--   The canonical discard depth discharges all finite startup hypotheses
--   once the shell is above `centralRenyiStartupScale`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L814-L907
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L814-L907

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

theorem CollatzEndpointTransport.FixedTotal.centralRenyi_startup
    {theta eta : ℝ}
    (htheta0 : 0 < theta)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    {M : ℕ} (hM : centralRenyiStartupScale theta eta ≤ M) :
    let K := centralRenyiDiscardDepth eta M
    K ≤ M ∧
    (K : ℝ) ≤ eta * M / 8 ∧
    4 ≤ eta * M ∧
    ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_exists_centralRenyi_linear_cutoff
-- name    : CollatzEndpointTransport.FixedTotal.exists_centralRenyi_linear_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:12.538174+00:00
-- url     : https://prove2.me/theorems/dc713acc-b9e2-566d-97c4-f23ac5e769c6
-- title:
--   Fixed Total: exists central Renyi linear cutoff
-- statement:
--   The central higher-Renyi rate dominates every fixed transport
--   coefficient below its limiting slope on a punctured neighborhood of zero.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L706-L750
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L706-L750

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

theorem CollatzEndpointTransport.FixedTotal.exists_centralRenyi_linear_cutoff
    {theta transport : ℝ}
    (htheta : 0 < theta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut : ℝ, 0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
          centralRenyiShellRate theta transport D / Real.log 2 := by sorry

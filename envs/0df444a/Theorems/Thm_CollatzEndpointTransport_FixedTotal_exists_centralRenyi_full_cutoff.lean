-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_exists_centralRenyi_full_cutoff
-- name    : CollatzEndpointTransport.FixedTotal.exists_centralRenyi_full_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:20.840182+00:00
-- url     : https://prove2.me/theorems/c4a42cbd-c4ba-5287-a72f-22eef17c2b90
-- title:
--   Fixed Total: exists central Renyi full cutoff
-- statement:
--   Small-density cutoff that simultaneously preserves the desired linear
--   transport and leaves enough exponential room to absorb both discarded
--   cohort terms.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L755-L797
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L755-L797

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

theorem CollatzEndpointTransport.FixedTotal.exists_centralRenyi_full_cutoff
    {theta transport eta : ℝ}
    (htheta : 0 < theta) (heta : 0 < eta)
    (htransport0 : 0 < transport)
    (htransport : transport < centralRenyiAsymptoticRate theta) :
    ∃ Dcut : ℝ, 0 < Dcut ∧ Dcut ≤ 1 ∧
      ∀ D : ℝ, 0 < D → D ≤ Dcut →
        transport * D ≤
            centralRenyiShellRate theta transport D / Real.log 2 ∧
        centralRenyiShellRate theta transport D ≤
            eta * Real.log 2 / 16 ∧
        centralRenyiShellRate theta transport D ≤ eta ^ 2 / 8 := by sorry

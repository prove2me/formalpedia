-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelCohortSet_subset_fixedSet
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_subset_fixedSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:00.594392+00:00
-- url     : https://prove2.me/theorems/0055fd81-25dc-570c-9967-b92ce758fbd1
-- title:
--   Fixed Total: central Level Cohort Set subset fixed Set
-- statement:
--   The Fixed Total construction uses the central Level Cohort Set subset fixed Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L225-L232
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L225-L232

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelCohortSet_subset_fixedSet
    {M s : ℕ} {theta eta : ℝ} (u : Fin M) :
    centralLevelCohortSet M s theta eta u ⊆
      fixedSet (M - (u : ℕ)) s := by sorry

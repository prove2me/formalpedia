-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelRenyiFactor_eq
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelRenyiFactor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:09:36.572511+00:00
-- url     : https://prove2.me/theorems/8b9755d1-647c-4abd-9e80-1cd9ba8a1d3e
-- title:
--   Fixed Total: central Level Renyi Factor eq
-- statement:
--   The Fixed Total construction uses the central Level Renyi Factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L342-L350
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L342-L350

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

theorem CollatzEndpointTransport.FixedTotal.centralLevelRenyiFactor_eq
    (M s : ℕ) (theta eta : ℝ) :
    ((((3 : ℝ) ^ (s + 1)) /
        (sourceOddLevel M s).card) ^ theta) *
      (∑ y ∈ centralLevelEndpointSet M s theta eta,
        (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) =
      centralLevelRenyiInformation M s theta eta := by sorry

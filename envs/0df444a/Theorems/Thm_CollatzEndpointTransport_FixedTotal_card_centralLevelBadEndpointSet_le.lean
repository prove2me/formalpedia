-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralLevelBadEndpointSet_le
-- name    : CollatzEndpointTransport.FixedTotal.card_centralLevelBadEndpointSet_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:09:47.843872+00:00
-- url     : https://prove2.me/theorems/f1e36784-7e19-47ed-ae89-564880f965b5
-- title:
--   Fixed Total: card central Level Bad Endpoint Set le
-- statement:
--   The Fixed Total construction uses the card central Level Bad Endpoint Set le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L261-L276
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiPullback.lean#L261-L276

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

theorem CollatzEndpointTransport.FixedTotal.card_centralLevelBadEndpointSet_le
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta : ℝ) :
    ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ≤
      C * (3 ^ (s + 1) : ℝ) ^ (1 - D) := by sorry

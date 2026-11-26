-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_card_rpow_le
-- name    : CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:18.065323+00:00
-- url     : https://prove2.me/theorems/d0b966b8-6464-4c19-b572-6fe2c1cd7b5c
-- title:
--   Fixed Total: binomial Annulus card rpow le
-- statement:
--   The cardinality contribution of every annulus has square-root scale.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L95-L122
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L95-L122

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000

theorem CollatzEndpointTransport.FixedTotal.binomialAnnulus_card_rpow_le
    {H j : ℕ} {theta : ℝ} (htheta0 : 0 < theta) :
    ((binomialAnnulus H j).card : ℝ) ^ theta ≤
      (8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2) := by sorry

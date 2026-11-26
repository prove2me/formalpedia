-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_subset_tails
-- name    : CollatzEndpointTransport.FixedTotal.binomialAnnulus_subset_tails
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:24.168356+00:00
-- url     : https://prove2.me/theorems/a74fcf45-3fa4-593f-aa9f-1932df81a31f
-- title:
--   Fixed Total: binomial Annulus subset tails
-- statement:
--   Every noncentral annulus lies in a pair of symmetric binomial tails.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L219-L254
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L219-L254

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000

theorem CollatzEndpointTransport.FixedTotal.binomialAnnulus_subset_tails
    {H j : ℕ} (_hj : 0 < j) :
    binomialAnnulus H j ⊆
      Finset.Ico 0 (binomialAnnulusCutoff H j + 1) ∪
        Finset.Ico (H - binomialAnnulusCutoff H j) (H + 1) := by sorry

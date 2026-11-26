-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_symmetricBinomialMass_annulus_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass_annulus_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:04.863519+00:00
-- url     : https://prove2.me/theorems/0951756b-a2ff-4aa2-a95e-9cc33036b28c
-- title:
--   Fixed Total: sum symmetric Binomial Mass annulus le
-- statement:
--   The total mass of annulus `j` is bounded by a fixed Gaussian profile.
--   The case `j = 0` uses only total mass one.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L292-L417
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMass.lean#L292-L417

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

theorem CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass_annulus_le
    {H j : ℕ} (hH : 0 < H) :
    (∑ k ∈ binomialAnnulus H j, symmetricBinomialMass H k) ≤
      2 * Real.exp (-2 * (j : ℝ) ^ 2) := by sorry

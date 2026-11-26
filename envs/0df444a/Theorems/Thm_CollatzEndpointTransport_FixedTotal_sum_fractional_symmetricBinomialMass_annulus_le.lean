-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fractional_symmetricBinomialMass_annulus_le
-- name    : CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_annulus_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:47.276377+00:00
-- url     : https://prove2.me/theorems/6b429b71-d0d3-4f79-8bd1-3d79bcf5bf6c
-- title:
--   Fixed Total: sum fractional symmetric Binomial Mass annulus le
-- statement:
--   Concavity and the Gaussian annulus-mass estimate, before summing annuli.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L125-L160
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L125-L160

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

theorem CollatzEndpointTransport.FixedTotal.sum_fractional_symmetricBinomialMass_annulus_le
    {H j : ℕ} {theta : ℝ}
    (hH : 0 < H) (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (∑ k ∈ binomialAnnulus H j,
        (symmetricBinomialMass H k) ^ (1 - theta)) ≤
      ((8 : ℝ) ^ theta * (H + 1 : ℝ) ^ (theta / 2)) *
        (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) := by sorry

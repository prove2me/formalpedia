-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_annular_fractional_decay_le_geometric
-- name    : CollatzEndpointTransport.FixedTotal.annular_fractional_decay_le_geometric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:50:26.670733+00:00
-- url     : https://prove2.me/theorems/247d8a13-ede3-40d0-9544-8dd44c46c9ac
-- title:
--   Fixed Total: annular fractional decay le geometric
-- statement:
--   The Gaussian annular profile is bounded by a geometric profile.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L163-L176
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean#L163-L176

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

theorem CollatzEndpointTransport.FixedTotal.annular_fractional_decay_le_geometric
    {j : ℕ} {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (2 * Real.exp (-2 * (j : ℝ) ^ 2)) ^ (1 - theta) ≤
      (2 : ℝ) ^ (1 - theta) *
        (Real.exp (-2 * (1 - theta))) ^ j := by sorry

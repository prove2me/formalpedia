-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_cast_le_raw
-- name    : CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:53.649504+00:00
-- url     : https://prove2.me/theorems/d88ddde1-a502-5eab-b6dc-4f733ab42385
-- title:
--   Fixed Total: actual Level Bad Mass cast le raw
-- statement:
--   The raw one-level heavy/ordinary decomposition.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalLevelBadMass.lean#L37-L109
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalLevelBadMass.lean#L37-L109

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFiberSplit
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le_raw
    (S : Set ℕ) (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by sorry

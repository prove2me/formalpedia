-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le_holder_raw
-- name    : CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_holder_raw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:22:15.695161+00:00
-- url     : https://prove2.me/theorems/4751627f-64c7-442e-b45c-efb980da31e6
-- title:
--   Fixed Total: central Level Bad Mass cast le holder raw
-- statement:
--   Direct finite Holder bound for the bad endpoint fibers at one odd-count
--   level.  This is the replacement for the heavy/ordinary split.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiTransport.lean#L126-L196
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiTransport.lean#L126-L196

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le_holder_raw
    (S : Set ℕ) (M s : ℕ) (theta eta : ℝ)
    (htheta : 0 < theta) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      ((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ^
          (theta / (1 + theta)) *
        (∑ y ∈ centralLevelEndpointSet M s theta eta,
          (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ^
            (1 / (1 + theta)) := by sorry

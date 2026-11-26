-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_eq_sum_bad
-- name    : CollatzEndpointTransport.FixedTotal.actualLevelBadMass_eq_sum_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:47.868885+00:00
-- url     : https://prove2.me/theorems/fe61d4fe-d389-5f64-9bd5-98240c938636
-- title:
--   Fixed Total: actual Level Bad Mass eq sum bad
-- statement:
--   The Fixed Total construction uses the actual Level Bad Mass eq sum bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalLevelBadMass.lean#L27-L34
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalLevelBadMass.lean#L27-L34

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFiberSplit
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.actualLevelBadMass_eq_sum_bad
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadMass S M s =
      ∑ y ∈ actualLevelBadEndpointSet S M s,
        actualLevelFiberCard M s y := by sorry

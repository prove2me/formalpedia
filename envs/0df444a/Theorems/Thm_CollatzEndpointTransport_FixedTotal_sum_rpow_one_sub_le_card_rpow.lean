-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_sub_le_card_rpow
-- name    : CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:11:50.814586+00:00
-- url     : https://prove2.me/theorems/9b276387-3795-4b38-a333-11e042c94439
-- title:
--   Fixed Total: sum rpow one sub le card rpow
-- statement:
--   Concavity of `x^(1-theta)` in the form used to aggregate fixed-total
--   source weights.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L152-L214
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L152-L214

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 20000

theorem CollatzEndpointTransport.FixedTotal.sum_rpow_one_sub_le_card_rpow
    {iota : Type*} (U : Finset iota) (p : iota → ℝ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hp : ∀ i ∈ U, 0 ≤ p i)
    (hpsum : ∑ i ∈ U, p i ≤ 1) :
    ∑ i ∈ U, (p i) ^ (1 - theta) ≤
      (U.card : ℝ) ^ theta := by sorry

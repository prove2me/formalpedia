-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_rpow_one_add_le_weighted
-- name    : CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:53.615987+00:00
-- url     : https://prove2.me/theorems/3fcece2d-36e7-4fb2-9eba-867053d1b7a3
-- title:
--   Fixed Total: sum rpow one add le weighted
-- statement:
--   Weighted convexity for a finite sum, with unused weight placed at zero.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L28-L80
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L28-L80

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

theorem CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le_weighted
    {ι : Type*} (U : Finset ι) (a w : ι → ℝ)
    {theta : ℝ} (htheta : 0 < theta)
    (ha : ∀ i ∈ U, 0 ≤ a i)
    (hw : ∀ i ∈ U, 0 < w i)
    (hwsum : ∑ i ∈ U, w i ≤ 1) :
    (∑ i ∈ U, a i) ^ (1 + theta) ≤
      ∑ i ∈ U, (w i) ^ (-theta) * (a i) ^ (1 + theta) := by sorry

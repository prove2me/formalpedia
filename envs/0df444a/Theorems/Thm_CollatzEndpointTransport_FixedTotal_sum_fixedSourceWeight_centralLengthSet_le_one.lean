-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_centralLengthSet_le_one
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_centralLengthSet_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:48.025655+00:00
-- url     : https://prove2.me/theorems/8e25f7f1-a521-4d9c-82f0-b3cc7b7972c2
-- title:
--   Fixed Total: sum fixed Source Weight central Length Set le one
-- statement:
--   The central fixed-total source weights have total mass at most one.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L217-L249
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L217-L249

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

theorem CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_centralLengthSet_le_one
    {N : ℕ} (hN : 0 < N) (eta : ℝ) :
    ∑ s ∈ centralLengthSet N eta, fixedSourceWeight N s ≤ 1 := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_residueFiber
-- name    : CollatzEndpointTransport.FixedTotal.sum_residueFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:55.07753+00:00
-- url     : https://prove2.me/theorems/4228b34e-dc7b-5b13-be8b-1658e7a50444
-- title:
--   Fixed Total: sum residue Fiber
-- statement:
--   Summing a function over all residue fibers recovers the sum over the
--   source set.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L232-L266
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L232-L266

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_residueFiber
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (hm : 0 < m) (f : α → β) :
    (∑ a : Fin m, ∑ x ∈ residueFiber W A m a, f x) =
      ∑ x ∈ W, f x := by sorry

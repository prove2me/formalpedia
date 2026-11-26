-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFiber_critical_bound
-- name    : CollatzEndpointTransport.FixedTotal.residueFiber_critical_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:08.397827+00:00
-- url     : https://prove2.me/theorems/ecd98584-651a-5944-9c26-be89f8cdc0ba
-- title:
--   Fixed Total: residue Fiber critical bound
-- statement:
--   Distinct lifts in a residue fiber obey the critical quotient-order
--   square-root bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L166-L228
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L166-L228

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.residueFiber_critical_bound
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (a : Fin m)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    Real.sqrt m *
        ((residueFiber W A m a).card : ℝ) *
        Real.sqrt (residueFiber W A m a).card ≤
      4 * ∑ x ∈ residueFiber W A m a,
        Real.sqrt (m + A x) := by sorry

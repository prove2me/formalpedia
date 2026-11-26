-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_quotient_injective_on_residueFiber
-- name    : CollatzEndpointTransport.FixedTotal.quotient_injective_on_residueFiber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:09.2116+00:00
-- url     : https://prove2.me/theorems/4062bb68-9fa1-463e-84b2-a87f159b2843
-- title:
--   Fixed Total: quotient injective on residue Fiber
-- statement:
--   The quotient map is injective inside one residue fiber when the integer
--   lift itself is injective.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L147-L162
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean#L147-L162

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.quotient_injective_on_residueFiber
    {α : Type*} [DecidableEq α]
    {W : Finset α} {A : α → ℕ} {m : ℕ} {a : Fin m}
    (hA : Set.InjOn A W) :
    Set.InjOn (fun x => A x / m) (residueFiber W A m a) := by sorry

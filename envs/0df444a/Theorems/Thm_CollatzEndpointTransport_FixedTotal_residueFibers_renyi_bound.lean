-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFibers_renyi_bound
-- name    : CollatzEndpointTransport.FixedTotal.residueFibers_renyi_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:48.902542+00:00
-- url     : https://prove2.me/theorems/92480f3a-884c-532d-baa2-76dd018d7348
-- title:
--   Fixed Total: residue Fibers renyi bound
-- statement:
--   Summed higher-order quotient estimate over all residue fibers.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L537-L567
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L537-L567

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.residueFibers_renyi_bound
    {alpha : Type*} [DecidableEq alpha]
    (W : Finset alpha) (A : alpha → ℕ) (m : ℕ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    (m : ℝ) ^ theta *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            ((residueFiber W A m a).card : ℝ) ^ theta) ≤
      4 * ∑ x ∈ W, ((m + A x : ℕ) : ℝ) ^ theta := by sorry

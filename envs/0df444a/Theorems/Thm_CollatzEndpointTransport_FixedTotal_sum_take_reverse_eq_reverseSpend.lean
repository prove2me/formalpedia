-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_take_reverse_eq_reverseSpend
-- name    : CollatzEndpointTransport.FixedTotal.sum_take_reverse_eq_reverseSpend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:58.718436+00:00
-- url     : https://prove2.me/theorems/2f87fc09-f5e2-45fe-b07a-3c53057ed180
-- title:
--   Fixed Total: sum take reverse eq reverse Spend
-- statement:
--   A prefix of the reversed block list has exactly the corresponding
--   terminal spend in the forward block list.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L979-L985
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L979-L985

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
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq

theorem CollatzEndpointTransport.FixedTotal.sum_take_reverse_eq_reverseSpend
    {N : ℕ} (c : Composition N) (r : ℕ) :
    (c.blocks.reverse.take r).sum = reverseSpend c r := by sorry

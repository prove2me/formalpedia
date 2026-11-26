-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseSpend_le
-- name    : CollatzEndpointTransport.FixedTotal.reverseSpend_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:32.922398+00:00
-- url     : https://prove2.me/theorems/3989101e-7ee8-4a2c-8c9f-d3dda479f817
-- title:
--   Fixed Total: reverse Spend le
-- statement:
--   The Fixed Total construction uses the reverse Spend le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1009-L1015
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1009-L1015

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

theorem CollatzEndpointTransport.FixedTotal.reverseSpend_le
    {N : ℕ} (c : Composition N) (r : ℕ) :
    reverseSpend c r ≤ N := by sorry

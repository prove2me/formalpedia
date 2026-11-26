-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalBlocks_length
-- name    : CollatzEndpointTransport.FixedTotal.terminalBlocks_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:42.298261+00:00
-- url     : https://prove2.me/theorems/8c49c05e-f9be-5ae6-9ff2-39eb78711356
-- title:
--   Fixed Total: terminal Blocks length
-- statement:
--   The Fixed Total construction uses the terminal Blocks length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L992-L999
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L992-L999

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

theorem CollatzEndpointTransport.FixedTotal.terminalBlocks_length
    {N : ℕ} (c : Composition N) {r : ℕ} (hr : r ≤ c.length) :
    (terminalBlocks c r).length = r := by sorry

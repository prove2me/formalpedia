-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_initialBlocks_append_terminalBlocks
-- name    : CollatzEndpointTransport.FixedTotal.initialBlocks_append_terminalBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:49.735022+00:00
-- url     : https://prove2.me/theorems/9da97d78-2cc4-4781-8d42-2b7038250cd7
-- title:
--   Fixed Total: initial Blocks append terminal Blocks
-- statement:
--   The Fixed Total construction uses the initial Blocks append terminal Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L987-L990
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L987-L990

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

theorem CollatzEndpointTransport.FixedTotal.initialBlocks_append_terminalBlocks
    {N : ℕ} (c : Composition N) (r : ℕ) :
    initialBlocks c r ++ terminalBlocks c r = c.blocks := by sorry

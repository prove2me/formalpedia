-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalBlocks_pos
-- name    : CollatzEndpointTransport.FixedTotal.terminalBlocks_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:51.370139+00:00
-- url     : https://prove2.me/theorems/273e8193-672f-5b55-9baf-17e83c0b2a85
-- title:
--   Fixed Total: terminal Blocks pos
-- statement:
--   The Fixed Total construction uses the terminal Blocks pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1034-L1038
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1034-L1038

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

theorem CollatzEndpointTransport.FixedTotal.terminalBlocks_pos
    {N : ℕ} (c : Composition N) (r : ℕ) :
    ∀ d ∈ terminalBlocks c r, 0 < d := by sorry

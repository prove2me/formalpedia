-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_subset_fixedBlockSet
-- name    : CollatzEndpointTransport.FixedTotal.terminalPatternSet_subset_fixedBlockSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:45.332005+00:00
-- url     : https://prove2.me/theorems/f86287c0-0eab-4ce8-8fae-f6d73b6aab71
-- title:
--   Fixed Total: terminal Pattern Set subset fixed Block Set
-- statement:
--   The Fixed Total construction uses the terminal Pattern Set subset fixed Block Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1233-L1253
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1233-L1253

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

theorem CollatzEndpointTransport.FixedTotal.terminalPatternSet_subset_fixedBlockSet
    {N s r D : ℕ} (hr : r ≤ s) :
    terminalPatternSet N s r D ⊆ fixedBlockSet D r := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalPatternSet_le
-- name    : CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:52.686264+00:00
-- url     : https://prove2.me/theorems/3ff55bed-c975-458f-9a0a-90f487dac88a
-- title:
--   Fixed Total: card terminal Pattern Set le
-- statement:
--   The Fixed Total construction uses the card terminal Pattern Set le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1255-L1261
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1255-L1261

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

theorem CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le
    {N s r D : ℕ} (hr : r ≤ s) :
    (terminalPatternSet N s r D).card ≤ (fixedSet D r).card := by sorry

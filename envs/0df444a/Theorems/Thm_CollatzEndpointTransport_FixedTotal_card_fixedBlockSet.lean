-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedBlockSet
-- name    : CollatzEndpointTransport.FixedTotal.card_fixedBlockSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:40.447358+00:00
-- url     : https://prove2.me/theorems/e53c254b-31bf-58de-9bf1-c8a360460fcc
-- title:
--   Fixed Total: card fixed Block Set
-- statement:
--   The Fixed Total construction uses the card fixed Block Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1157-L1163
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1157-L1163

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

theorem CollatzEndpointTransport.FixedTotal.card_fixedBlockSet (D r : ℕ) :
    (fixedBlockSet D r).card = (fixedSet D r).card := by sorry

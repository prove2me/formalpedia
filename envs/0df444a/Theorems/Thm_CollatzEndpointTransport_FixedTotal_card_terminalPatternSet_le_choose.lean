-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalPatternSet_le_choose
-- name    : CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:20.255822+00:00
-- url     : https://prove2.me/theorems/e71081ec-b4ba-435e-b54a-383b437cdfc4
-- title:
--   Fixed Total: card terminal Pattern Set le choose
-- statement:
--   The Fixed Total construction uses the card terminal Pattern Set le choose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1263-L1269
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1263-L1269

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

theorem CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le_choose
    {N s r D : ℕ} (hr : r ≤ s) (hD : 0 < D) (hr0 : 0 < r) :
    (terminalPatternSet N s r D).card ≤ (D - 1).choose (r - 1) := by sorry

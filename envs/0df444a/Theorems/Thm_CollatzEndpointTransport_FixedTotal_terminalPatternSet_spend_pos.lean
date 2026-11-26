-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_pos
-- name    : CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:53.4291+00:00
-- url     : https://prove2.me/theorems/2f51c51d-12f9-57cf-8fb4-f55f4ba01185
-- title:
--   Fixed Total: terminal Pattern Set spend pos
-- statement:
--   The Fixed Total construction uses the terminal Pattern Set spend pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1271-L1287
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1271-L1287

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

theorem CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_pos
    {N s r D : ℕ} (hr0 : 0 < r) (hrs : r ≤ s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    0 < D := by sorry

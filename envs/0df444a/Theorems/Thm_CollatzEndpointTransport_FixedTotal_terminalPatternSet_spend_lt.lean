-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_lt
-- name    : CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:33:52.469926+00:00
-- url     : https://prove2.me/theorems/c84ca67b-448e-5356-a263-17bfaf496671
-- title:
--   Fixed Total: terminal Pattern Set spend lt
-- statement:
--   The Fixed Total construction uses the terminal Pattern Set spend lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1289-L1300
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1289-L1300

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

theorem CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_lt
    {N s r D : ℕ} (hrs : r < s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    D < N := by sorry

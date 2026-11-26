-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_eq_empty_of_spend_lt
-- name    : CollatzEndpointTransport.FixedTotal.terminalPatternSet_eq_empty_of_spend_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:14.856567+00:00
-- url     : https://prove2.me/theorems/8e3de100-153a-48f3-9f17-d4d4f5469d63
-- title:
--   Fixed Total: terminal Pattern Set eq empty of spend lt
-- statement:
--   The Fixed Total construction uses the terminal Pattern Set eq empty of spend lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1331-L1337
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1331-L1337

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

theorem CollatzEndpointTransport.FixedTotal.terminalPatternSet_eq_empty_of_spend_lt
    {N s r D : ℕ} (hrs : r ≤ s) (hDr : D < r) :
    terminalPatternSet N s r D = ∅ := by sorry

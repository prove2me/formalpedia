-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_bounds
-- name    : CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:45.289028+00:00
-- url     : https://prove2.me/theorems/6c0a96b4-0601-5509-a2d1-008472d92d09
-- title:
--   Fixed Total: terminal Pattern Set spend bounds
-- statement:
--   Positivity of the terminal blocks and of the remaining prefix gives
--   the two stars-and-bars spend bounds.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1304-L1329
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1304-L1329

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

theorem CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_bounds
    {N s r D : ℕ} (hrs : r ≤ s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    r ≤ D ∧ s - r ≤ N - D := by sorry

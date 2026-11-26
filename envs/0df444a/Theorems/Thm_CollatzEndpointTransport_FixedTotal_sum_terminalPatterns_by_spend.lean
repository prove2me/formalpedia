-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_terminalPatterns_by_spend
-- name    : CollatzEndpointTransport.FixedTotal.sum_terminalPatterns_by_spend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:15.2067+00:00
-- url     : https://prove2.me/theorems/24f11b9a-69a5-5a58-a367-4929b7dd360d
-- title:
--   Fixed Total: sum terminal Patterns by spend
-- statement:
--   Partition terminal patterns by their total reverse spend.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1204-L1231
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1204-L1231

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

theorem CollatzEndpointTransport.FixedTotal.sum_terminalPatterns_by_spend
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : ℕ → List ℕ → R) :
    (∑ d ∈ terminalPatternImage N s r, f d.sum d) =
      ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D, f D d := by sorry

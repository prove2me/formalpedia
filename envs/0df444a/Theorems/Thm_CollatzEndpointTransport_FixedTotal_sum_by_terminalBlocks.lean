-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_by_terminalBlocks
-- name    : CollatzEndpointTransport.FixedTotal.sum_by_terminalBlocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:26.895931+00:00
-- url     : https://prove2.me/theorems/28512fd8-3a91-4d77-b90a-7dc196120499
-- title:
--   Fixed Total: sum by terminal Blocks
-- statement:
--   Partition a composition sum by its exact terminal block list.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1175-L1201
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1175-L1201

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

theorem CollatzEndpointTransport.FixedTotal.sum_by_terminalBlocks
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : List ℕ → R) :
    (∑ c ∈ fixedSet N s, f (terminalBlocks c r)) =
      ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card * f d := by sorry

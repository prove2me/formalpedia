-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalFiber_le
-- name    : CollatzEndpointTransport.FixedTotal.card_terminalFiber_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:37.117642+00:00
-- url     : https://prove2.me/theorems/17661ba7-6c4d-5b13-b24c-36a42cc901fd
-- title:
--   Fixed Total: card terminal Fiber le
-- statement:
--   A prescribed terminal list leaves at most the number of compatible
--   fixed-total prefixes.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1126-L1139
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1126-L1139

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

theorem CollatzEndpointTransport.FixedTotal.card_terminalFiber_le
    {N s r : ℕ} (d : List ℕ) :
    (terminalFiber N s r d).card ≤
      (fixedSet (N - d.sum) (s - r)).card := by sorry

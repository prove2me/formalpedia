-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalFiber_le_choose
-- name    : CollatzEndpointTransport.FixedTotal.card_terminalFiber_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:09.774389+00:00
-- url     : https://prove2.me/theorems/64acf29f-bbd6-5feb-8a4b-5869092b7a74
-- title:
--   Fixed Total: card terminal Fiber le choose
-- statement:
--   Stars-and-bars form of the terminal-fiber upper bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1142-L1151
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1142-L1151

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

theorem CollatzEndpointTransport.FixedTotal.card_terminalFiber_le_choose
    {N s r : ℕ} (d : List ℕ)
    (hprefixTotal : 0 < N - d.sum) (hprefixLength : 0 < s - r) :
    (terminalFiber N s r d).card ≤
      (N - d.sum - 1).choose (s - r - 1) := by sorry

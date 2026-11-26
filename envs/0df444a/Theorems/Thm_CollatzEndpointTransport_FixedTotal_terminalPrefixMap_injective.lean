-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPrefixMap_injective
-- name    : CollatzEndpointTransport.FixedTotal.terminalPrefixMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:31:28.708235+00:00
-- url     : https://prove2.me/theorems/0e7195cb-24bb-5cd1-975a-d129a1e20436
-- title:
--   Fixed Total: terminal Prefix Map injective
-- statement:
--   The Fixed Total construction uses the terminal Prefix Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1106-L1122
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiCore.lean#L1106-L1122

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

theorem CollatzEndpointTransport.FixedTotal.terminalPrefixMap_injective
    {N s r : ℕ} (d : List ℕ) :
    Function.Injective (terminalPrefixMap (N := N) (s := s) (r := r) d) := by sorry

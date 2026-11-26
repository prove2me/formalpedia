-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_lowerLengthPowSum_formula
-- name    : CollatzEndpointTransport.FixedTotal.lowerLengthPowSum_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:14.979029+00:00
-- url     : https://prove2.me/theorems/f7e9c385-0577-54df-94ef-50375e06b71b
-- title:
--   Fixed Total: lower Length Pow Sum formula
-- statement:
--   The Fixed Total construction uses the lower Length Pow Sum formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L116-L134
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L116-L134

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.lowerLengthPowSum_formula
    (N : ℕ) (hN : 0 < N) :
    (∑ c : Composition N, 3 ^ (c.length - 1)) = 4 ^ (N - 1) := by sorry

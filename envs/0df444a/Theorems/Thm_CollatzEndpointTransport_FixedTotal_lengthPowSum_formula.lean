-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_lengthPowSum_formula
-- name    : CollatzEndpointTransport.FixedTotal.lengthPowSum_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:30.534828+00:00
-- url     : https://prove2.me/theorems/2708f3cd-2939-41c1-9b92-8c3bf1c2af34
-- title:
--   Fixed Total: length Pow Sum formula
-- statement:
--   The Fixed Total construction uses the length Pow Sum formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L103-L114
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean#L103-L114

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.lengthPowSum_formula
    (N : ℕ) (hN : 0 < N) :
    lengthPowSum N = 3 * 4 ^ (N - 1) := by sorry

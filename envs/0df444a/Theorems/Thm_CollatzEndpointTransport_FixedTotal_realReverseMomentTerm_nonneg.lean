-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMomentTerm_nonneg
-- name    : CollatzEndpointTransport.FixedTotal.realReverseMomentTerm_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:33.54524+00:00
-- url     : https://prove2.me/theorems/6c03fca7-e140-5cc1-a9d1-8940f94e5d1e
-- title:
--   Fixed Total: real Reverse Moment Term nonneg
-- statement:
--   The Fixed Total construction uses the real Reverse Moment Term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L305-L309
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L305-L309

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.realReverseMomentTerm_nonneg
    (theta : ℝ) {N : ℕ} (c : Composition N) (r : ℕ) :
    0 ≤ realReverseMomentTerm theta c r := by sorry

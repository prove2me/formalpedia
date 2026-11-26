-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_coe_reverseMomentTerm_eq_realReverseMomentTerm
-- name    : CollatzEndpointTransport.FixedTotal.coe_reverseMomentTerm_eq_realReverseMomentTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:35.451247+00:00
-- url     : https://prove2.me/theorems/fec13f83-6c44-4044-8997-c2f59f464537
-- title:
--   Fixed Total: coe reverse Moment Term eq real Reverse Moment Term
-- statement:
--   The Fixed Total construction uses the coe reverse Moment Term eq real Reverse Moment Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L296-L303
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L296-L303

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

theorem CollatzEndpointTransport.FixedTotal.coe_reverseMomentTerm_eq_realReverseMomentTerm
    {theta : ℝ} {N : ℕ} (c : Composition N) {r : ℕ} (hr : 0 < r) :
    (reverseMomentTerm theta c.blocks.reverse (r - 1) : ℝ) =
      realReverseMomentTerm theta c r := by sorry

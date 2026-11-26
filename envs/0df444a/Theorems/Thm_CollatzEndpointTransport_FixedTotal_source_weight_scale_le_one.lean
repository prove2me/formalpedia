-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_le_one
-- name    : CollatzEndpointTransport.FixedTotal.source_weight_scale_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:53.763285+00:00
-- url     : https://prove2.me/theorems/9430eea9-ef53-4251-a88b-8d6e81b3e43e
-- title:
--   Fixed Total: source weight scale le one
-- statement:
--   The Fixed Total construction uses the source weight scale le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1418-L1429
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1418-L1429

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.source_weight_scale_le_one
    {N s : ℕ} {theta : ℝ}
    (hcard : 0 < (fixedSet N s).card)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    fixedSourceWeight N s *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) ≤ 1 := by sorry

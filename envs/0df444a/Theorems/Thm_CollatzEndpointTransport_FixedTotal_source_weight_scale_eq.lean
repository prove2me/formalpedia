-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_source_weight_scale_eq
-- name    : CollatzEndpointTransport.FixedTotal.source_weight_scale_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:52.835725+00:00
-- url     : https://prove2.me/theorems/297344f4-5f22-5b53-ba11-7d21922efe81
-- title:
--   Fixed Total: source weight scale eq
-- statement:
--   The Fixed Total construction uses the source weight scale eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1399-L1416
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L1399-L1416

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

theorem CollatzEndpointTransport.FixedTotal.source_weight_scale_eq
    {N s : ℕ} {theta : ℝ}
    (hcard : 0 < (fixedSet N s).card)
    (htheta : theta < 1) :
    fixedSourceWeight N s *
        ((((2 : ℝ) ^ N) ^ theta) /
          (((fixedSet N s).card : ℝ) ^ theta)) =
      (fixedSourceWeight N s) ^ (1 - theta) := by sorry

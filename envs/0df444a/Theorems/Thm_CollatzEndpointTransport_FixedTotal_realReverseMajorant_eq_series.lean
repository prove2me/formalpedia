-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMajorant_eq_series
-- name    : CollatzEndpointTransport.FixedTotal.realReverseMajorant_eq_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:09.227364+00:00
-- url     : https://prove2.me/theorems/1f784b95-27f6-5409-8229-92adf88d85a7
-- title:
--   Fixed Total: real Reverse Majorant eq series
-- statement:
--   The Fixed Total construction uses the real Reverse Majorant eq series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L877-L900
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L877-L900

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

theorem CollatzEndpointTransport.FixedTotal.realReverseMajorant_eq_series
    {N s : ℕ} (theta : ℝ) (c : Composition N)
    (hc : c ∈ fixedSet N s) :
    realReverseMajorant theta c =
      (∑ r ∈ Ico 1 (s + 1), realReverseMomentTerm theta c r) +
        (((3 : ℝ) ^ theta) ^ s /
          (((2 : ℝ) ^ N) ^ theta)) := by sorry

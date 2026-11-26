-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMoment_tail_cons
-- name    : CollatzEndpointTransport.FixedTotal.reverseMoment_tail_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:24.026033+00:00
-- url     : https://prove2.me/theorems/c97ea0e3-2228-474c-b7f7-41edb429398e
-- title:
--   Fixed Total: reverse Moment tail cons
-- statement:
--   The Fixed Total construction uses the reverse Moment tail cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L187-L201
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L187-L201

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
open Finset
open scoped NNReal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.reverseMoment_tail_cons
    (theta : ℝ) (k : ℕ) (ks : List ℕ) :
    ((3 : ℝ≥0) ^ theta) ^ (k :: ks).length /
        (((2 : ℝ≥0) ^ (k :: ks).sum) ^ theta) =
      ((3 : ℝ≥0) ^ theta) /
          (((2 : ℝ≥0) ^ k) ^ theta) *
        (((3 : ℝ≥0) ^ theta) ^ ks.length /
          (((2 : ℝ≥0) ^ ks.sum) ^ theta)) := by sorry

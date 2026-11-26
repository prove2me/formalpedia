-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
-- name    : CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:14.64262+00:00
-- url     : https://prove2.me/theorems/84d8ca2c-f199-57da-bab3-9707466179d7
-- title:
--   Fixed Total: reverse Moment Majorant cons
-- statement:
--   The Fixed Total construction uses the reverse Moment Majorant cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L150-L153
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L150-L153

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

theorem CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons (theta : ℝ) (k : ℕ) (ks : List ℕ) :
    reverseMomentMajorant theta (k :: ks) =
      (1 + (3 : ℝ≥0) ^ theta * reverseMomentMajorant theta ks) /
        (((2 : ℝ≥0) ^ k) ^ theta) := by sorry

attribute [defeq] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

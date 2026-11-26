-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentTerm_cons_zero
-- name    : CollatzEndpointTransport.FixedTotal.reverseMomentTerm_cons_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:10.621151+00:00
-- url     : https://prove2.me/theorems/b488cc22-e1a9-53f9-a317-220d1fe080f5
-- title:
--   Fixed Total: reverse Moment Term cons zero
-- statement:
--   The Fixed Total construction uses the reverse Moment Term cons zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L166-L170
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L166-L170

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

theorem CollatzEndpointTransport.FixedTotal.reverseMomentTerm_cons_zero
    (theta : ℝ) (k : ℕ) (ks : List ℕ) :
    reverseMomentTerm theta (k :: ks) 0 =
      1 / (((2 : ℝ≥0) ^ k) ^ theta) := by sorry

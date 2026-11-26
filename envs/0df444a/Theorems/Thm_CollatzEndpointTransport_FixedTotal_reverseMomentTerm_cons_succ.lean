-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentTerm_cons_succ
-- name    : CollatzEndpointTransport.FixedTotal.reverseMomentTerm_cons_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:12.524551+00:00
-- url     : https://prove2.me/theorems/948ebeda-a8bb-4d82-90c4-bdb3d0e06232
-- title:
--   Fixed Total: reverse Moment Term cons succ
-- statement:
--   The Fixed Total construction uses the reverse Moment Term cons succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L172-L185
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L172-L185

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

theorem CollatzEndpointTransport.FixedTotal.reverseMomentTerm_cons_succ
    (theta : ℝ) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    reverseMomentTerm theta (k :: ks) (i + 1) =
      ((3 : ℝ≥0) ^ theta) /
          (((2 : ℝ≥0) ^ k) ^ theta) *
        reverseMomentTerm theta ks i := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_eq_series
-- name    : CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_eq_series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:38.779799+00:00
-- url     : https://prove2.me/theorems/afb72f4c-a88c-40fc-b3be-3573e4787980
-- title:
--   Fixed Total: reverse Moment Majorant eq series
-- statement:
--   The Fixed Total construction uses the reverse Moment Majorant eq series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L203-L221
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L203-L221

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

theorem CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_eq_series (theta : ℝ) :
    ∀ ks : List ℕ,
      reverseMomentMajorant theta ks = reverseMomentSeries theta ks := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_cons
-- name    : CollatzEndpointTransport.FixedTotal.normalizedReverseLift_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:07.702259+00:00
-- url     : https://prove2.me/theorems/ec32f668-256d-55b7-9274-6662bb7ff5e0
-- title:
--   Fixed Total: normalized Reverse Lift cons
-- statement:
--   The Fixed Total construction uses the normalized Reverse Lift cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L127-L136
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L127-L136

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

theorem CollatzEndpointTransport.FixedTotal.normalizedReverseLift_cons (k : ℕ) (ks : List ℕ) :
    normalizedReverseLift (k :: ks) =
      (1 + 3 * normalizedReverseLift ks) / ((2 : ℝ≥0) ^ k) := by sorry

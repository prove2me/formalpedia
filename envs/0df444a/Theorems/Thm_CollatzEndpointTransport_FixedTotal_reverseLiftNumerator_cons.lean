-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
-- name    : CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:17.456523+00:00
-- url     : https://prove2.me/theorems/b6cad15d-f7c7-50bf-a81a-4ad8d9f525f1
-- title:
--   Fixed Total: reverse Lift Numerator cons
-- statement:
--   The Fixed Total construction uses the reverse Lift Numerator cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L40-L42
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L40-L42

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons (k : ℕ) (ks : List ℕ) :
    reverseLiftNumerator (k :: ks) =
      3 * reverseLiftNumerator ks + 2 ^ ks.sum := by sorry

attribute [defeq] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons

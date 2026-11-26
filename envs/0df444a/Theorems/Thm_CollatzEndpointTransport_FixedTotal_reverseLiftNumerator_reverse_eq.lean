-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_reverse_eq
-- name    : CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_reverse_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:10.964833+00:00
-- url     : https://prove2.me/theorems/0b96c8c3-1673-4f94-bf79-26ba86bf14d4
-- title:
--   Fixed Total: reverse Lift Numerator reverse eq
-- statement:
--   Exact reverse recursion for `3^length + A`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L77-L89
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L77-L89

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_reverse_eq (ks : List ℕ) :
    reverseLiftNumerator ks.reverse =
      3 ^ ks.length + syracuseNumeratorList ks := by sorry

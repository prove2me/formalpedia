-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedNumerator_injective
-- name    : CollatzEndpointTransport.FixedTotal.fixedNumerator_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:10.6366+00:00
-- url     : https://prove2.me/theorems/220d4df2-f4d2-5182-a833-cb0ba3886cc0
-- title:
--   Fixed Total: fixed Numerator injective
-- statement:
--   Integer-lift injectivity in the fixed-total model.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L238-L247
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L238-L247

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.fixedNumerator_injective
    {N s : ℕ} :
    Function.Injective (fixedNumerator : FixedComposition N s → ℕ) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_injective_of_length_sum
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_injective_of_length_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:57.77133+00:00
-- url     : https://prove2.me/theorems/31f30498-965c-530e-9557-df8f9990caf3
-- title:
--   Fixed Total: syracuse Numerator List injective of length sum
-- statement:
--   Integer-lift injectivity for positive lists of fixed length and total.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L99-L176
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L99-L176

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_injective_of_length_sum
    (s : ℕ) :
    ∀ {ks ls : List ℕ},
      ks.length = s →
      ls.length = s →
      (∀ k ∈ ks, 0 < k) →
      (∀ l ∈ ls, 0 < l) →
      ks.sum = ls.sum →
      syracuseNumeratorList ks = syracuseNumeratorList ls →
      ks = ls := by sorry

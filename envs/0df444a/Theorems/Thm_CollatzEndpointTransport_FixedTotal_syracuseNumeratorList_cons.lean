-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:27.459902+00:00
-- url     : https://prove2.me/theorems/a4f3f929-b767-52f6-9812-8fc362a06382
-- title:
--   Fixed Total: syracuse Numerator List cons
-- statement:
--   The Fixed Total construction uses the syracuse Numerator List cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L41-L43
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L41-L43

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons (k : ℕ) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) =
      3 ^ ks.length + 2 ^ k * syracuseNumeratorList ks := by sorry

attribute [defeq] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons

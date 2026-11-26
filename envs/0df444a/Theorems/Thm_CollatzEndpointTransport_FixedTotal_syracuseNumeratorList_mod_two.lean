-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_mod_two
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_mod_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:36.375829+00:00
-- url     : https://prove2.me/theorems/106877dd-67fa-4e11-b21d-9e620470420f
-- title:
--   Fixed Total: syracuse Numerator List mod two
-- statement:
--   A nonempty positive valuation list has odd Syracuse numerator.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L52-L67
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L52-L67

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_mod_two
    {k : ℕ} (hk : 0 < k) (ks : List ℕ) :
    syracuseNumeratorList (k :: ks) % 2 = 1 := by sorry

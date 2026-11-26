-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injective_on_length
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumerator_injective_on_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:00.544682+00:00
-- url     : https://prove2.me/theorems/ecd28a87-46d2-507a-8ebe-fb69cf811361
-- title:
--   Fixed Total: syracuse Numerator injective on length
-- statement:
--   **Integer-lift injectivity.**
--
--   At fixed total `N` and fixed number of parts `s`, distinct positive
--   compositions have distinct integer Syracuse numerators.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L186-L200
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalComposition.lean#L186-L200

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.syracuseNumerator_injective_on_length
    {N s : ℕ} {c d : Composition N}
    (hc : c.length = s) (hd : d.length = s)
    (hnum : syracuseNumerator c = syracuseNumerator d) :
    c = d := by sorry

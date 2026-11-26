-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_append_singleton_central
-- name    : CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_append_singleton_central
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:04.427286+00:00
-- url     : https://prove2.me/theorems/a856a0b3-d422-419c-a123-c82ff061d4a7
-- title:
--   Fixed Total: syracuse Numerator List append singleton central
-- statement:
--   Appending the final valuation part gives the matching forward
--   numerator recursion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L46-L56
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiReverse.lean#L46-L56

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat

theorem CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_append_singleton_central
    (ks : List ℕ) (k : ℕ) :
    syracuseNumeratorList (ks ++ [k]) =
      3 * syracuseNumeratorList ks + 2 ^ ks.sum := by sorry

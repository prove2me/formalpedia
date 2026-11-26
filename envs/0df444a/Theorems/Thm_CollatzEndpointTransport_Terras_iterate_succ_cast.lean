-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_iterate_succ_cast
-- name    : CollatzEndpointTransport.Terras.iterate_succ_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:05.797866+00:00
-- url     : https://prove2.me/theorems/74d4f299-ef82-5c4b-b794-a9d94aab768d
-- title:
--   Terras: iterate succ cast
-- statement:
--   Real one-step recurrence at time `k`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L125-L132
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L125-L132

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.iterate_succ_cast (k n : ℕ) :
    ((T^[k + 1]) n : ℝ) =
      ((3 : ℝ) ^ (if parityBit ((T^[k]) n) then 1 else 0) *
          ((T^[k]) n : ℝ) +
        parityDigitR n k) / 2 := by sorry

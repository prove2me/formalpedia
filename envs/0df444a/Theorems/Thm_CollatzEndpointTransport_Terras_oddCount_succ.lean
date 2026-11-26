-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_succ
-- name    : CollatzEndpointTransport.Terras.oddCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:11:58.004376+00:00
-- url     : https://prove2.me/theorems/23099cfb-9717-5087-a376-c0aa087af567
-- title:
--   Terras: odd Count succ
-- statement:
--   One more iterate adds exactly the current parity digit to the odd count.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L55-L60
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L55-L60

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.oddCount_succ (k n : ℕ) :
    oddCount (k + 1) n =
      oddCount k n +
        if parityBit ((T^[k]) n) then 1 else 0 := by sorry

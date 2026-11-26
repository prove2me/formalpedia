-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_add
-- name    : CollatzEndpointTransport.Terras.oddCount_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:26:11.56611+00:00
-- url     : https://prove2.me/theorems/7f289a5b-b9dd-4c9b-af4c-51001e947179
-- title:
--   Terras: odd Count add
-- statement:
--   Odd counts concatenate exactly across consecutive iterate blocks.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L164-L177
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L164-L177

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.oddCount_add (k d n : ℕ) :
    oddCount (k + d) n =
      oddCount k n + oddCount d ((T^[k]) n) := by sorry

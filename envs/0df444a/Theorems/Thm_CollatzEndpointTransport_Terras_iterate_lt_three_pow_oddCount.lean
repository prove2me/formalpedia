-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_iterate_lt_three_pow_oddCount
-- name    : CollatzEndpointTransport.Terras.iterate_lt_three_pow_oddCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:56.919051+00:00
-- url     : https://prove2.me/theorems/45b15a20-3034-4172-8df2-09b9b36efa86
-- title:
--   Terras: iterate lt three pow odd Count
-- statement:
--   Terminal form of `iterate_lt_three_pow_mul_remaining`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L156-L161
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L156-L161

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.iterate_lt_three_pow_oddCount
    {M n : ℕ} (hn : n < 2 ^ M) :
    (T^[M]) n < 3 ^ oddCount M n := by sorry

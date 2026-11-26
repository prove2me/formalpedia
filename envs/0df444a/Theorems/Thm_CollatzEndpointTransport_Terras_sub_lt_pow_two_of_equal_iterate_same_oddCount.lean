-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_sub_lt_pow_two_of_equal_iterate_same_oddCount
-- name    : CollatzEndpointTransport.Terras.sub_lt_pow_two_of_equal_iterate_same_oddCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:35.188945+00:00
-- url     : https://prove2.me/theorems/88a55fd1-739b-4946-bf58-65b0cbc6b79f
-- title:
--   Terras: sub lt pow two of equal iterate same odd Count
-- statement:
--   Two ordered inputs with the same odd count and the same `d`-step output
--   must have started less than one source block-width apart.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L181-L218
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L181-L218

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.sub_lt_pow_two_of_equal_iterate_same_oddCount
    {d k n m : ℕ}
    (hnm : n < m)
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    m - n < 2 ^ d := by sorry

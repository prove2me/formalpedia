-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_dist_lt_pow_two_of_equal_iterate_same_oddCount
-- name    : CollatzEndpointTransport.Terras.dist_lt_pow_two_of_equal_iterate_same_oddCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:58.125711+00:00
-- url     : https://prove2.me/theorems/1e6e2653-557f-5c3a-8cd3-8d7972609d78
-- title:
--   Terras: dist lt pow two of equal iterate same odd Count
-- statement:
--   Symmetric distance form of
--   `sub_lt_pow_two_of_equal_iterate_same_oddCount`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L222-L236
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L222-L236

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.dist_lt_pow_two_of_equal_iterate_same_oddCount
    {d k n m : ℕ}
    (hnk : oddCount d n = k)
    (hmk : oddCount d m = k)
    (hout : (T^[d]) n = (T^[d]) m) :
    n.dist m < 2 ^ d := by sorry

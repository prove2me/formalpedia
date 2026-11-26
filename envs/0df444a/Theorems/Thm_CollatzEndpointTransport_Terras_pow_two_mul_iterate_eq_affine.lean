-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_pow_two_mul_iterate_eq_affine
-- name    : CollatzEndpointTransport.Terras.pow_two_mul_iterate_eq_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:02.837799+00:00
-- url     : https://prove2.me/theorems/2b66434f-4c90-5f6b-8b15-e6f6eb37dc5d
-- title:
--   Terras: pow two mul iterate eq affine
-- statement:
--   **Exact integer affine iterate identity.**
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L48-L84
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L48-L84

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.pow_two_mul_iterate_eq_affine (k n : ℕ) :
    2 ^ k * (T^[k]) n =
      3 ^ oddCount k n * n + integerCorrection k n := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_lt_scale
-- name    : CollatzEndpointTransport.Terras.integerCorrection_lt_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:17.985722+00:00
-- url     : https://prove2.me/theorems/e3237550-be80-5579-8320-e4a9f95ab6fc
-- title:
--   Terras: integer Correction lt scale
-- statement:
--   The integer correction is always smaller than one full affine output
--   unit at the same odd-count level.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L88-L115
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L88-L115

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.integerCorrection_lt_scale (k n : ℕ) :
    integerCorrection k n <
      3 ^ oddCount k n * 2 ^ k := by sorry

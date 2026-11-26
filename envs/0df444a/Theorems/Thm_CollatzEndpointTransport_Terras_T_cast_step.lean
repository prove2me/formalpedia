-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_T_cast_step
-- name    : CollatzEndpointTransport.Terras.T_cast_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:13:37.227747+00:00
-- url     : https://prove2.me/theorems/8c25a2f7-fb2a-48dc-bbe4-470a56b91755
-- title:
--   Terras: T cast step
-- statement:
--   Real form of one half-Collatz step, with the parity digit explicit.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L102-L122
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L102-L122

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.T_cast_step (x : ℕ) :
    (T x : ℝ) =
      ((3 : ℝ) ^ (if parityBit x then 1 else 0) * x +
        (if parityBit x then 1 else 0)) / 2 := by sorry

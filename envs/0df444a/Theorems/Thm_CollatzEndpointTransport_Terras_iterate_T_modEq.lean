-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_iterate_T_modEq
-- name    : CollatzEndpointTransport.Terras.iterate_T_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:51.698805+00:00
-- url     : https://prove2.me/theorems/bd06cd5d-3bf8-444b-9080-31b66bf3801a
-- title:
--   Terras: iterate T mod Eq
-- statement:
--   `i` steps of `T` consume exactly `i` bits.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L80-L91
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L80-L91

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.iterate_T_modEq :
    ∀ (i j n n' : ℕ), n ≡ n' [MOD 2 ^ (i + j)] →
      T^[i] n ≡ T^[i] n' [MOD 2 ^ j] := by sorry

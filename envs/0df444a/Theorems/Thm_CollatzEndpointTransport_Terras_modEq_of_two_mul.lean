-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_modEq_of_two_mul
-- name    : CollatzEndpointTransport.Terras.modEq_of_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:51.596701+00:00
-- url     : https://prove2.me/theorems/a17b93aa-09f5-443e-8229-ceb1e516e0f7
-- title:
--   Terras: mod Eq of two mul
-- statement:
--   Halving a congruence: `2a ≡ 2b [MOD 2^(H+1)]` gives `a ≡ b [MOD 2^H]`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L53-L61
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L53-L61

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.modEq_of_two_mul {H a b : ℕ}
    (h : 2 * a ≡ 2 * b [MOD 2 ^ (H + 1)]) : a ≡ b [MOD 2 ^ H] := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_parityVec_congr
-- name    : CollatzEndpointTransport.Terras.parityVec_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:49.069296+00:00
-- url     : https://prove2.me/theorems/cf517438-05fa-5619-8deb-04e9351ed995
-- title:
--   Terras: parity Vec congr
-- statement:
--   **Terras, well-definedness.** The parity vector depends only on
--   `n % 2 ^ H`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L101-L110
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L101-L110

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.parityVec_congr {H n n' : ℕ} (h : n ≡ n' [MOD 2 ^ H]) :
    parityVec H n = parityVec H n' := by sorry

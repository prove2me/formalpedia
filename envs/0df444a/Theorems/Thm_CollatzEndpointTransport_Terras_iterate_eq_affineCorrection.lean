-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_iterate_eq_affineCorrection
-- name    : CollatzEndpointTransport.Terras.iterate_eq_affineCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:36.783207+00:00
-- url     : https://prove2.me/theorems/1aa91337-59ae-4bf8-ad4a-993c37224bfc
-- title:
--   Terras: iterate eq affine Correction
-- statement:
--   **Exact affine iterate identity.**
--
--   This is the precise Lean form of
--
--   `T^k(m) = (m/2^k + r_k(m)) 3^(sum_{i<k} p_i(m))`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L140-L156
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L140-L156

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.iterate_eq_affineCorrection (k n : ℕ) :
    ((T^[k]) n : ℝ) =
      ((n : ℝ) / (2 : ℝ) ^ k + affineCorrection k n) *
        (3 : ℝ) ^ oddCount k n := by sorry

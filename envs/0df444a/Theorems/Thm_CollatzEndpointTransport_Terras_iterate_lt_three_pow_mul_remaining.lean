-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_iterate_lt_three_pow_mul_remaining
-- name    : CollatzEndpointTransport.Terras.iterate_lt_three_pow_mul_remaining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:36.580969+00:00
-- url     : https://prove2.me/theorems/4218cef9-0b9a-5e4e-af42-bcb88dee80bd
-- title:
--   Terras: iterate lt three pow mul remaining
-- statement:
--   A residue below `2^M` stays below its exact multiplicative odd-step
--   scale after any prefix of the `M`-step window.  At the terminal prefix this
--   is the sharp canonical-residue endpoint bound
--
--   `T^[M] n < 3 ^ oddCount M n`.
--
--   The extra factor `2^(M-j)` is the remaining source precision.  Keeping it in
--   the induction is what makes the estimate uniform in `M`, rather than a
--   finite-depth calculation.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L126-L153
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L126-L153

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.iterate_lt_three_pow_mul_remaining
    {M n j : ℕ} (hjM : j ≤ M) (hn : n < 2 ^ M) :
    (T^[j]) n < 3 ^ oddCount j n * 2 ^ (M - j) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_lowerBinomialSum_le
-- name    : CollatzEndpointTransport.Terras.pow_mul_lowerBinomialSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:47.965477+00:00
-- url     : https://prove2.me/theorems/f3b80eb9-2395-4356-abe6-d8c042ecfaaf
-- title:
--   Terras: pow mul lower Binomial Sum le
-- statement:
--   The elementary lower-tail generating-function bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L43-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L43-L64

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.pow_mul_lowerBinomialSum_le
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K * (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H := by sorry

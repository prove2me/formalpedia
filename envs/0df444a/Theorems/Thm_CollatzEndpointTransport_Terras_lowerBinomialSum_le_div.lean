-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_div
-- name    : CollatzEndpointTransport.Terras.lowerBinomialSum_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:59.659973+00:00
-- url     : https://prove2.me/theorems/eb0ad20a-0f76-5ba6-9104-ae3e791e0b73
-- title:
--   Terras: lower Binomial Sum le div
-- statement:
--   Division form of `pow_mul_lowerBinomialSum_le`, valid for `x > 0`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L67-L72
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L67-L72

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.lowerBinomialSum_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H / x ^ K := by sorry

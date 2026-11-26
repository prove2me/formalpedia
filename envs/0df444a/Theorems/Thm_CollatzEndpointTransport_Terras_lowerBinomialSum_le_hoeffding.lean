-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_lowerBinomialSum_le_hoeffding
-- name    : CollatzEndpointTransport.Terras.lowerBinomialSum_le_hoeffding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:07.139986+00:00
-- url     : https://prove2.me/theorems/014634e8-2e44-4bae-9807-6eb1714203df
-- title:
--   Terras: lower Binomial Sum le hoeffding
-- statement:
--   Explicit lower binomial-tail estimate with Hoeffding exponent `2t^2H`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L108-L168
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L108-L168

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.lowerBinomialSum_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (lowerBinomialSum H K : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by sorry

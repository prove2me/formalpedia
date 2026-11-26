-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_correction_loss_lt_half
-- name    : CollatzEndpointTransport.QuantitativeDensity.correction_loss_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:30.699258+00:00
-- url     : https://prove2.me/theorems/562f8e33-9c45-4505-bbf6-885cfc307b25
-- title:
--   Quantitative Density: correction loss lt half
-- statement:
--   **Correction loss.** The correction exponent loses at most
--   `max delta ((1 + delta) * zeta + delta * log_2 3)`; the second argument
--   dominates, and it too is below `t/2`.
--
--   The two terms are `m^delta` and
--   `3^delta * m^((1 + delta) zeta + delta log_2 3)`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L144-L159
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L144-L159

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.correction_loss_lt_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + kappa * t) * (kappa * t) + kappa * t * lg3 < t / 2 := by sorry

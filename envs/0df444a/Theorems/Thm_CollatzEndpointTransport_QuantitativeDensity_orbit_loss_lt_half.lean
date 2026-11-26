-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_orbit_loss_lt_half
-- name    : CollatzEndpointTransport.QuantitativeDensity.orbit_loss_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:33.640997+00:00
-- url     : https://prove2.me/theorems/ed015906-78dc-4c9b-a6bd-90712c871679
-- title:
--   Quantitative Density: orbit loss lt half
-- statement:
--   **Orbit loss.** With `delta = zeta = kappa * t`, the orbit exponent loses
--   `delta + a_0 * zeta + delta * zeta`, and this is below `t/2`.
--
--   This is `(1 + delta)(1 + zeta) - b * zeta`, expanded using `1 - b = a_0`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L127-L136
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L127-L136

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.orbit_loss_lt_half {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    kappa * t + a0 * (kappa * t) + kappa * t * (kappa * t) < t / 2 := by sorry

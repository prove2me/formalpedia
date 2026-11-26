-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_admissibleExponent_strictAnti
-- name    : CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_strictAnti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:52.394843+00:00
-- url     : https://prove2.me/theorems/6c4e9f74-c141-526f-9b31-21bd7e8f837a
-- title:
--   Quantitative Density: admissible Exponent strict Anti
-- statement:
--   `a_max(q)` is strictly decreasing on `(0,1)`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L226-L238
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L226-L238

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_strictAnti
    {q₁ q₂ : ℝ} (hq₁0 : 0 < q₁) (hq₁q₂ : q₁ < q₂) (_hq₂1 : q₂ < 1) :
    admissibleExponent q₂ < admissibleExponent q₁ := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_admissibleExponent_lt_headline
-- name    : CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_lt_headline
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:28.544798+00:00
-- url     : https://prove2.me/theorems/9245db73-0635-5334-85f1-a90d4a5bacbc
-- title:
--   Quantitative Density: admissible Exponent lt headline
-- statement:
--   Every admissible `q > a_0` gives a strict exponent below the headline
--   constant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L242-L246
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L242-L246

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_lt_headline
    {q : ℝ} (hqa : a0 < q) (hq1 : q < 1) :
    admissibleExponent q < headlineExponent := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_admissibleExponent_tendsto_headline
-- name    : CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_tendsto_headline
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:01.376821+00:00
-- url     : https://prove2.me/theorems/9f1045f0-2db7-50e5-8221-70a3153bdeff
-- title:
--   Quantitative Density: admissible Exponent tendsto headline
-- statement:
--   Gate D in endpoint form: the admissible exponents converge to the
--   headline constant as `q -> a_0` from above. Together with
--   `admissibleExponent_lt_headline`, this is the exact open-interval supremum
--   statement.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L262-L274
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L262-L274

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.admissibleExponent_tendsto_headline :
    Filter.Tendsto admissibleExponent
      (nhdsWithin a0 (Set.Ioi a0)) (nhds headlineExponent) := by sorry

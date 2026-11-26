-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_exponentCondition_iff
-- name    : CollatzEndpointTransport.QuantitativeDensity.exponentCondition_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:19:28.847816+00:00
-- url     : https://prove2.me/theorems/f56db81a-6db5-47a2-a0de-fbc4bc4e732c
-- title:
--   Quantitative Density: exponent Condition iff
-- statement:
--   **Gate F.** The document's condition
--   `a < log(1/q)/log 3` is exactly `a * gamma(q) < 1`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L288-L307
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L288-L307

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.exponentCondition_iff
    {a q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    a < admissibleExponent q ↔ a * gammaExponent q < 1 := by sorry

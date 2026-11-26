-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_kappa_mul_cq_mul
-- name    : CollatzEndpointTransport.QuantitativeDensity.kappa_mul_cq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:40.186363+00:00
-- url     : https://prove2.me/theorems/6432855a-58a4-5cbd-9ba5-15774b18b3c2
-- title:
--   Quantitative Density: kappa mul cq mul
-- statement:
--   **The `c_q` identity.** At the cap `t = c_q * lambda_(j+1)` with
--   `lambda_(j+1) = q * lambda_j`, the tolerance `delta = kappa * t` equals
--   exactly `lambda_j * (q - a_0) / 4`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L169-L174
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L169-L174

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.kappa_mul_cq_mul (q : ℝ) (hq : 0 < q) :
    kappa * cq q * q = (q - a0) / 4 := by sorry

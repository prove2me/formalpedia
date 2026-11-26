-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_cap_clears_requirement
-- name    : CollatzEndpointTransport.QuantitativeDensity.cap_clears_requirement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:17:58.718784+00:00
-- url     : https://prove2.me/theorems/a7ef7319-cf61-5779-8b4b-2bf4c628f65a
-- title:
--   Quantitative Density: cap clears requirement
-- statement:
--   **The cap clears the requirement.** The bootstrap needs
--   `delta <= lambda (q - a_0) / (2 (1 - lambda))`; the cap supplies
--   `lambda (q - a_0) / 4`. Since `0 < lambda < 1`, the cap is strictly smaller,
--   so it clears the requirement by a factor of at least two, uniformly in `j`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L186-L192
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L186-L192

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity

theorem CollatzEndpointTransport.QuantitativeDensity.cap_clears_requirement
    {lam q : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < 1) (hqa : a0 < q) :
    lam * (q - a0) / 4 < lam * (q - a0) / (2 * (1 - lam)) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_lg3_one_lt
-- name    : CollatzEndpointTransport.Terras.lg3_one_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:29.499037+00:00
-- url     : https://prove2.me/theorems/d0d25b13-8d66-4735-8434-62384465c1ac
-- title:
--   Terras: lg3 one lt
-- statement:
--   Elementary lower bound used by the maximal-barrier startup arithmetic.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L314-L319
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativeDensityConstants.lean#L314-L319

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.lg3_one_lt : 1 < QuantitativeDensity.lg3 := by sorry

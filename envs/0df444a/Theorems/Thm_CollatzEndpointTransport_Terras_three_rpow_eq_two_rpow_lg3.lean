-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_three_rpow_eq_two_rpow_lg3
-- name    : CollatzEndpointTransport.Terras.three_rpow_eq_two_rpow_lg3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:11.979558+00:00
-- url     : https://prove2.me/theorems/15b3541a-caab-491b-a4f7-58bc0a2d73f7
-- title:
--   Terras: three rpow eq two rpow lg3
-- statement:
--   Change of base for real powers, specialized to `log_2 3`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L45-L54
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L45-L54

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real

theorem CollatzEndpointTransport.Terras.three_rpow_eq_two_rpow_lg3 (x : ℝ) :
    (3 : ℝ) ^ x =
      (2 : ℝ) ^ (QuantitativeDensity.lg3 * x) := by sorry

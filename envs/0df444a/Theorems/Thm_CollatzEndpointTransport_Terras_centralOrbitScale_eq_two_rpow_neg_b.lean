-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_centralOrbitScale_eq_two_rpow_neg_b
-- name    : CollatzEndpointTransport.Terras.centralOrbitScale_eq_two_rpow_neg_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:18:55.689976+00:00
-- url     : https://prove2.me/theorems/00d905a0-3b8f-432f-a6eb-29cd13439c82
-- title:
--   Terras: central Orbit Scale eq two rpow neg b
-- statement:
--   The Terras construction uses the central Orbit Scale eq two rpow neg b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L56-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L56-L64

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real

theorem CollatzEndpointTransport.Terras.centralOrbitScale_eq_two_rpow_neg_b (k : ℕ) :
    centralOrbitScale k =
      (2 : ℝ) ^ (-QuantitativeDensity.bConst * k) := by sorry

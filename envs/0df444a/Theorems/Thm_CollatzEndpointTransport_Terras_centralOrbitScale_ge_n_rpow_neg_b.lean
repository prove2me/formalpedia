-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_centralOrbitScale_ge_n_rpow_neg_b
-- name    : CollatzEndpointTransport.Terras.centralOrbitScale_ge_n_rpow_neg_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:30.955304+00:00
-- url     : https://prove2.me/theorems/abc25a44-6cba-5c72-9f0c-0fe2dd57d548
-- title:
--   Terras: central Orbit Scale ge n rpow neg b
-- statement:
--   The Terras construction uses the central Orbit Scale ge n rpow neg b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L66-L97
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L66-L97

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real

theorem CollatzEndpointTransport.Terras.centralOrbitScale_ge_n_rpow_neg_b
    {n k M : ℕ}
    (hkM : k ≤ M)
    (hnShell : n ∈ Finset.Ico (2 ^ M) (2 ^ (M + 1))) :
    (n : ℝ) ^ (-QuantitativeDensity.bConst) ≤
      centralOrbitScale k := by sorry

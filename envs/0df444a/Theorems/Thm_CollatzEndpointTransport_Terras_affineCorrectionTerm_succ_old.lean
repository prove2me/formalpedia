-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_succ_old
-- name    : CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_old
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:15.019375+00:00
-- url     : https://prove2.me/theorems/85cb6b7c-83a1-4852-b1e3-5d2b507e867c
-- title:
--   Terras: affine Correction Term succ old
-- statement:
--   Every old correction summand gains exactly one additional factor of two
--   in its denominator when the horizon is increased.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L64-L71
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L64-L71

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_old
    {k n i : ℕ} (hi : i < k) :
    affineCorrectionTerm (k + 1) n i =
      affineCorrectionTerm k n i / 2 := by sorry

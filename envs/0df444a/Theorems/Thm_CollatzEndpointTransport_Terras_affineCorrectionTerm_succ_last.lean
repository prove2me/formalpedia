-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrectionTerm_succ_last
-- name    : CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:00.20634+00:00
-- url     : https://prove2.me/theorems/5efb901a-169e-546d-ab79-ac6baae20b10
-- title:
--   Terras: affine Correction Term succ last
-- statement:
--   The final correction summand at horizon `k+1`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L74-L78
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L74-L78

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affineCorrectionTerm_succ_last (k n : ℕ) :
    affineCorrectionTerm (k + 1) n k =
      parityDigitR n k /
        ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrection_succ
-- name    : CollatzEndpointTransport.Terras.affineCorrection_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:08.173522+00:00
-- url     : https://prove2.me/theorems/35fc8722-9429-5bc7-9226-292b5c0ec402
-- title:
--   Terras: affine Correction succ
-- statement:
--   Autonomous one-step recurrence for the affine correction.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L81-L99
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L81-L99

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affineCorrection_succ (k n : ℕ) :
    affineCorrection (k + 1) n =
      affineCorrection k n / 2 +
        parityDigitR n k /
          ((3 : ℝ) ^ oddCount (k + 1) n * 2) := by sorry

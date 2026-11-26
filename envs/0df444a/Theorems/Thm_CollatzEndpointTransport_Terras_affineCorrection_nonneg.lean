-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_affineCorrection_nonneg
-- name    : CollatzEndpointTransport.Terras.affineCorrection_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:49.835826+00:00
-- url     : https://prove2.me/theorems/550213d2-7b60-5434-a931-2cdddd6dd0f2
-- title:
--   Terras: affine Correction nonneg
-- statement:
--   The Terras construction uses the affine Correction nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L49-L51
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L49-L51

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.affineCorrection_nonneg (k n : ℕ) :
    0 ≤ affineCorrection k n := by sorry

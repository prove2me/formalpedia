-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrection_parityVec
-- name    : CollatzEndpointTransport.FixedTotal.wordCorrection_parityVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:15.992146+00:00
-- url     : https://prove2.me/theorems/d91fcd71-d3df-4178-b06a-db2eb042e80e
-- title:
--   Fixed Total: word Correction parity Vec
-- statement:
--   The recursively defined orbit correction is exactly the correction of
--   the corresponding Terras parity word.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L160-L176
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean#L160-L176

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset

theorem CollatzEndpointTransport.FixedTotal.wordCorrection_parityVec
    (M n : ℕ) :
    wordCorrectionFrom 0 0 (List.ofFn (Terras.parityVec M n)) =
      Terras.integerCorrection M n := by sorry

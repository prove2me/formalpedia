-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_parityDigitR_le_one
-- name    : CollatzEndpointTransport.Terras.parityDigitR_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:44.492044+00:00
-- url     : https://prove2.me/theorems/d29477f1-c1c6-583c-b673-d3da9a9a8ab7
-- title:
--   Terras: parity Digit R le one
-- statement:
--   The Terras construction uses the parity Digit R le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L32-L33
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L32-L33

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.parityDigitR_le_one (n i : ℕ) : parityDigitR n i ≤ 1 := by sorry

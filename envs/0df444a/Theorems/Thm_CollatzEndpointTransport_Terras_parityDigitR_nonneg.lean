-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_parityDigitR_nonneg
-- name    : CollatzEndpointTransport.Terras.parityDigitR_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:08:34.609814+00:00
-- url     : https://prove2.me/theorems/bfa51957-f6d3-5bdb-bc77-f405b562b3a6
-- title:
--   Terras: parity Digit R nonneg
-- statement:
--   The Terras construction uses the parity Digit R nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L29-L30
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrection.lean#L29-L30

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.parityDigitR_nonneg (n i : ℕ) : 0 ≤ parityDigitR n i := by sorry

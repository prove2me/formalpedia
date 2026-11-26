-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_succ
-- name    : CollatzEndpointTransport.Terras.integerCorrection_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:09.118463+00:00
-- url     : https://prove2.me/theorems/ecddf58d-2aad-4845-9c30-8d6d81b556a1
-- title:
--   Terras: integer Correction succ
-- statement:
--   The Terras construction uses the integer Correction succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L40-L45
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasIntegerAffine.lean#L40-L45

import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.integerCorrection_succ (k n : ℕ) :
    integerCorrection (k + 1) n =
      if parityBit ((T^[k]) n) then
        3 * integerCorrection k n + 2 ^ k
      else
        integerCorrection k n := by sorry

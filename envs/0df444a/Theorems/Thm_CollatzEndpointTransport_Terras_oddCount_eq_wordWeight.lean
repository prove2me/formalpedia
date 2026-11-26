-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_wordWeight
-- name    : CollatzEndpointTransport.Terras.oddCount_eq_wordWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:07:00.677004+00:00
-- url     : https://prove2.me/theorems/d33589c3-4f29-4b7a-930d-505dc8dd123f
-- title:
--   Terras: odd Count eq word Weight
-- statement:
--   The Terras construction uses the odd Count eq word Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L181-L182
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L181-L182

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.oddCount_eq_wordWeight (H n : ℕ) :
    oddCount H n = wordWeight (parityVec H n) := by sorry

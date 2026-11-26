-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_sum_range
-- name    : CollatzEndpointTransport.Terras.oddCount_eq_sum_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:12:11.009719+00:00
-- url     : https://prove2.me/theorems/5e3d1430-340d-461f-9998-ba352fb8258f
-- title:
--   Terras: odd Count eq sum range
-- statement:
--   `oddCount` is the sum of the parity digits over the corresponding
--   natural-number range.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L39-L52
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasAffineIterate.lean#L39-L52

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.oddCount_eq_sum_range (H n : ℕ) :
    oddCount H n =
      ∑ i ∈ Finset.range H,
        if parityBit ((T^[i]) n) then 1 else 0 := by sorry

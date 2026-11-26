-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_parityLowerCutoff_cast_le
-- name    : CollatzEndpointTransport.Terras.parityLowerCutoff_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:20.000109+00:00
-- url     : https://prove2.me/theorems/c229bea0-827e-5925-9d17-1a6d56b06897
-- title:
--   Terras: parity Lower Cutoff cast le
-- statement:
--   The Terras construction uses the parity Lower Cutoff cast le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasPrefixEvents.lean#L27-L31
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasPrefixEvents.lean#L27-L31

import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.parityLowerCutoff_cast_le
    {t : ℝ} (htHalf : t ≤ 1 / 2) (H : ℕ) :
    (parityLowerCutoff t H : ℝ) ≤ (1 / 2 - t) * H := by sorry

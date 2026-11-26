-- Prove2me | Theorems.Thm_BandParity_isPrimitiveRoot_gi
-- name    : BandParity.isPrimitiveRoot_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:23.677713+00:00
-- url     : https://prove2.me/theorems/9fdd4b15-afad-5d49-a67b-101147c63dc3
-- title:
--   Band Parity: is Primitive Root gi
-- statement:
--   The Band Parity construction uses the is Primitive Root gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L19-L25
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Pin.lean#L19-L25

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_Pin
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.isPrimitiveRoot_gi : IsPrimitiveRoot gi 4 := by sorry

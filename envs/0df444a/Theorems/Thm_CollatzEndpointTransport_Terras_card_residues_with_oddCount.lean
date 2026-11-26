-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:48.405707+00:00
-- url     : https://prove2.me/theorems/65b00ad4-6048-5099-b5f6-c87c8a636f5a
-- title:
--   Terras: card residues with odd Count
-- statement:
--   The Terras construction uses the card residues with odd Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L218-L242
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L218-L242

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount (H k : ℕ) :
    (Finset.univ.filter
      (fun x : Fin (2 ^ H) => oddCount H (x : ℕ) = k)).card = H.choose k := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:54.958918+00:00
-- url     : https://prove2.me/theorems/81713ce9-1c5e-5a74-bf39-465ff0ca6a1e
-- title:
--   Terras: card residues with odd Count le
-- statement:
--   Exact count of residues whose first `H` Collatz parity bits contain at
--   most `K` odd steps.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L172-L207
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L172-L207

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_le (H K : ℕ) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card =
      lowerBinomialSum H K := by sorry

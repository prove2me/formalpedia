-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub_le_hoeffding
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_le_hoeffding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:40.594349+00:00
-- url     : https://prove2.me/theorems/f4aef38f-e2c7-5b35-bb63-bb541ef7cdc3
-- title:
--   Terras: card residues with odd Count ge sub le hoeffding
-- statement:
--   Explicit Hoeffding bound for the symmetric upper Collatz parity tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L332-L346
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L332-L346

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by sorry

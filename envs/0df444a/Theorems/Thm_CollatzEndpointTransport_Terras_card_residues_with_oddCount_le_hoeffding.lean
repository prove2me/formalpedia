-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le_hoeffding
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_hoeffding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:33.222796+00:00
-- url     : https://prove2.me/theorems/568b41b1-0b83-5eb6-b5f7-6bffface5fa8
-- title:
--   Terras: card residues with odd Count le hoeffding
-- statement:
--   Explicit Hoeffding bound for the lower Collatz parity tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L230-L237
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L230-L237

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_hoeffding
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ H * Real.exp (-2 * t ^ 2 * H) := by sorry

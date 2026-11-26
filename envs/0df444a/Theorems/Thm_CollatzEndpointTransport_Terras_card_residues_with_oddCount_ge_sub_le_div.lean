-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub_le_div
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_le_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:45.322825+00:00
-- url     : https://prove2.me/theorems/b21ddec1-b9ab-488f-a6ec-b03b149c42f4
-- title:
--   Terras: card residues with odd Count ge sub le div
-- statement:
--   Division form of the symmetric upper Collatz residue tail bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L323-L329
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L323-L329

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (1 + x) ^ H / x ^ K := by sorry

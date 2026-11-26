-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le_div
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:02.727162+00:00
-- url     : https://prove2.me/theorems/7752eb82-bf21-4e2b-a528-d232feff9a08
-- title:
--   Terras: card residues with odd Count le div
-- statement:
--   Division form of the exact Collatz residue tail bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L221-L227
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L221-L227

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    ((Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H / x ^ K := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_le_div_pow_le_exp
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div_pow_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:52.37572+00:00
-- url     : https://prove2.me/theorems/83a673ca-f0a9-423b-a7c3-4bf0069d5f96
-- title:
--   Terras: card residues with odd Count le div pow le exp
-- statement:
--   Normalized lower-tail proportion among all `2^H` residues.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L240-L248
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L240-L248

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_le_div_pow_le_exp
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
        (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) /
        (2 : ℝ) ^ H ≤
      Real.exp (-2 * t ^ 2 * H) := by sorry

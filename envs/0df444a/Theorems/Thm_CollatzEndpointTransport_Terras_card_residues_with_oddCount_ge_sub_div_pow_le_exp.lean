-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub_div_pow_le_exp
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_div_pow_le_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:30.624314+00:00
-- url     : https://prove2.me/theorems/d009386d-c779-5b9f-a94e-d364a2171098
-- title:
--   Terras: card residues with odd Count ge sub div pow le exp
-- statement:
--   Normalized symmetric upper-tail proportion among all `2^H` residues.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L349-L358
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L349-L358

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub_div_pow_le_exp
    {H K : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    ((Finset.univ.filter
        (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) /
        (2 : ℝ) ^ H ≤
      Real.exp (-2 * t ^ 2 * H) := by sorry

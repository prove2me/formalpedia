-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_card_residues_with_oddCount_ge_sub
-- name    : CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_ge_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:24:24.775275+00:00
-- url     : https://prove2.me/theorems/95228dad-492c-52d7-82ad-6b27183a21a1
-- title:
--   Terras: pow mul card residues with odd Count ge sub
-- statement:
--   The symmetric upper Collatz residue tail satisfies the same weighted
--   generating-function bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L313-L320
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L313-L320

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_ge_sub
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card : ℝ) ≤
      (1 + x) ^ H := by sorry

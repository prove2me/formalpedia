-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_card_residues_with_oddCount_le
-- name    : CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:45.413816+00:00
-- url     : https://prove2.me/theorems/6771bbbc-c76c-5802-ac62-0c26a2870b4d
-- title:
--   Terras: pow mul card residues with odd Count le
-- statement:
--   The exact Collatz residue tail satisfies the same weighted bound as the
--   abstract binomial tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L211-L218
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L211-L218

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.pow_mul_card_residues_with_oddCount_le
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K *
        ((Finset.univ.filter
          (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card : ℝ) ≤
      (1 + x) ^ H := by sorry

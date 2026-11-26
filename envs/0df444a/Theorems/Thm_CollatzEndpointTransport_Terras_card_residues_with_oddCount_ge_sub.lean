-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount_ge_sub
-- name    : CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:58.364242+00:00
-- url     : https://prove2.me/theorems/1b4e3c5b-b32b-45ef-a2a1-2d15c6efe853
-- title:
--   Terras: card residues with odd Count ge sub
-- statement:
--   Exact count of the symmetric upper tail: at least `H - K` odd steps.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L261-L309
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean#L261-L309

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub
    (H K : ℕ) (hKH : K ≤ H) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card =
      lowerBinomialSum H K := by sorry

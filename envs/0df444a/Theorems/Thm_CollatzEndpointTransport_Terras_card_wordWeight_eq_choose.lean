-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_wordWeight_eq_choose
-- name    : CollatzEndpointTransport.Terras.card_wordWeight_eq_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:06:58.70449+00:00
-- url     : https://prove2.me/theorems/6c6f1423-7879-4640-a0c2-47301877ec6f
-- title:
--   Terras: card word Weight eq choose
-- statement:
--   **Exact binomial count.** The residues mod `2 ^ H` whose first `H` steps
--   contain exactly `k` odd steps number exactly `H.choose k`.
--
--   This is the precise sense in which the odd count is `Binomial (H, 1/2)` under
--   uniform residues: it is a counting identity, with no probabilistic hypothesis
--   and no independence assumption.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L190-L216
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasParityBijection.lean#L190-L216

import Mathlib
import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_wordWeight_eq_choose (H k : ℕ) :
    (Finset.univ.filter (fun v : Fin H → Bool => wordWeight v = k)).card
      = H.choose k := by sorry

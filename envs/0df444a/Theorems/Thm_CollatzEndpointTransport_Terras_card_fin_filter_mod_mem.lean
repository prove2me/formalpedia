-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_fin_filter_mod_mem
-- name    : CollatzEndpointTransport.Terras.card_fin_filter_mod_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:50.446804+00:00
-- url     : https://prove2.me/theorems/df7fa577-16a4-4c14-9667-28bf551382b4
-- title:
--   Terras: card fin filter mod mem
-- statement:
--   In `Fin (blocks * q)`, every residue modulo a positive `q` occurs
--   exactly `blocks` times.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L31-L63
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L31-L63

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_fin_filter_mod_mem
    {blocks q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    (Finset.univ.filter
      (fun x : Fin (blocks * q) =>
        (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by sorry

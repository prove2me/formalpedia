-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_filter_mod_mem
-- name    : CollatzEndpointTransport.Terras.card_dyadic_shell_filter_mod_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:49.334245+00:00
-- url     : https://prove2.me/theorems/ec003283-903f-47ec-925b-953b7cf0608f
-- title:
--   Terras: card dyadic shell filter mod mem
-- statement:
--   **Exact dyadic-shell repetition.** If `H <= M`, every selected residue
--   modulo `2^H` occurs exactly `2^(M-H)` times in
--   `[2^M, 2^(M+1))`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L176-L193
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L176-L193

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_dyadic_shell_filter_mod_mem
    {H M : ℕ} (hHM : H ≤ M) (S : Finset (Fin (2 ^ H))) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n =>
        (⟨n % (2 ^ H), Nat.mod_lt _ (pow_pos (by omega) _)⟩ :
          Fin (2 ^ H)) ∈ S)).card =
      2 ^ (M - H) * S.card := by sorry

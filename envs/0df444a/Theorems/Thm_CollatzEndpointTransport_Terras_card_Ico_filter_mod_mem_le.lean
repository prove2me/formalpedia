-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_Ico_filter_mod_mem_le
-- name    : CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:29.013987+00:00
-- url     : https://prove2.me/theorems/447840d6-7c13-41ee-90eb-27581721f42f
-- title:
--   Terras: card Ico filter mod mem le
-- statement:
--   A periodic residue family occupies at most one extra incomplete period
--   in an arbitrary interval.  This is the division-free form of
--   `density + one-period boundary error`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L124-L171
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L124-L171

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_le
    {base length q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    ((Finset.Ico base (base + length)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card ≤
      (length / q + 1) * S.card := by sorry

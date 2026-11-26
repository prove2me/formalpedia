-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_Ico_filter_mod_mem_of_dvd
-- name    : CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:39.419665+00:00
-- url     : https://prove2.me/theorems/69b9c980-2851-4649-91b1-0a9268ba702a
-- title:
--   Terras: card Ico filter mod mem of dvd
-- statement:
--   A periodic predicate has its exact expected count on an interval made
--   of complete periods, provided the interval starts at a period boundary.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L67-L119
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L67-L119

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_of_dvd
    {base blocks q : ℕ} (hq : 0 < q) (hbase : q ∣ base)
    (S : Finset (Fin q)) :
    ((Finset.Ico base (base + blocks * q)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by sorry

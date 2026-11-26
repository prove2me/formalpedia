-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_le
-- name    : CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:41.074134+00:00
-- url     : https://prove2.me/theorems/93017b2a-9d6b-5fff-a5c5-effc0cafbea6
-- title:
--   Terras: card dyadic shell odd Count le
-- statement:
--   Exact shell count for a lower odd-count tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L205-L226
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L205-L226

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le
    {H M K : ℕ} (hHM : H ≤ M) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by sorry

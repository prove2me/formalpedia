-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_ge_sub
-- name    : CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:54.616496+00:00
-- url     : https://prove2.me/theorems/8ef9883d-537f-499e-a63d-7772ed5e6853
-- title:
--   Terras: card dyadic shell odd Count ge sub
-- statement:
--   Exact shell count for the symmetric upper odd-count tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L250-L271
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L250-L271

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub
    {H M K : ℕ} (hHM : H ≤ M) (hKH : K ≤ H) :
    ((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card =
      2 ^ (M - H) * lowerBinomialSum H K := by sorry

-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_le_hoeffding
-- name    : CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le_hoeffding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:55.450813+00:00
-- url     : https://prove2.me/theorems/32758093-3b54-5a2c-b0c8-d8dab9ca2964
-- title:
--   Terras: card dyadic shell odd Count le hoeffding
-- statement:
--   **Shell Hoeffding bound.** In the exact-repetition regime `H <= M`,
--   the lower parity tail occupies at most an `exp (-2 t^2 H)` fraction of the
--   dyadic shell.  There is no shell-transfer error term.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L231-L247
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L231-L247

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_le_hoeffding
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => oddCount H n ≤ K)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by sorry

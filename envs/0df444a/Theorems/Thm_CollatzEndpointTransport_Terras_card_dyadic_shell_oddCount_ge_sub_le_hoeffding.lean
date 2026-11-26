-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_dyadic_shell_oddCount_ge_sub_le_hoeffding
-- name    : CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub_le_hoeffding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:59.545428+00:00
-- url     : https://prove2.me/theorems/68021cd9-2506-5fdd-8c12-4a0c20891aa5
-- title:
--   Terras: card dyadic shell odd Count ge sub le hoeffding
-- statement:
--   The symmetric upper parity tail has the same shell Hoeffding bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L274-L297
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasShellRepetition.lean#L274-L297

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras

theorem CollatzEndpointTransport.Terras.card_dyadic_shell_oddCount_ge_sub_le_hoeffding
    {H M K : ℕ} {t : ℝ} (hHM : H ≤ M) (ht : 0 ≤ t)
    (hcut : (K : ℝ) ≤ (1 / 2 - t) * H) :
    (((Finset.Ico (2 ^ M) (2 ^ (M + 1))).filter
      (fun n => H - K ≤ oddCount H n)).card : ℝ) ≤
      (2 : ℝ) ^ M * Real.exp (-2 * t ^ 2 * H) := by sorry

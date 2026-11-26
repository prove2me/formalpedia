-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_card_shellParityPrefixBadAt_le
-- name    : CollatzEndpointTransport.Terras.card_shellParityPrefixBadAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:55.734937+00:00
-- url     : https://prove2.me/theorems/d33996e3-ed54-475c-b539-c24089f56ce8
-- title:
--   Terras: card shell Parity Prefix Bad At le
-- statement:
--   One horizon contributes at most twice the one-sided Hoeffding tail.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasPrefixEvents.lean#L51-L86
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasPrefixEvents.lean#L51-L86

import Mathlib.Algebra.Order.Floor.Semiring
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset

theorem CollatzEndpointTransport.Terras.card_shellParityPrefixBadAt_le
    {M H : ℕ} {t : ℝ} (hHM : H ≤ M)
    (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((shellParityPrefixBadAt M H t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * H)) := by sorry

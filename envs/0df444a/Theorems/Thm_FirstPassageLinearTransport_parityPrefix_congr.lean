-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityPrefix_congr
-- name    : FirstPassageLinearTransport.parityPrefix_congr
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:27.253478+00:00
-- url     : https://prove2.me/theorems/c5e3545b-f287-5a98-a8d8-2a2821e92bb7
-- title:
--   First Passage Linear Transport: parity Prefix congr
-- statement:
--   The first `M` parity bits depend only on the residue modulo `2^M`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L86-L98
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L86-L98

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.parityPrefix_congr {M n n' : ℕ}
    (h : n ≡ n' [MOD 2 ^ M]) :
    (fun i : Fin M => parityBit n i) =
      (fun i : Fin M => parityBit n' i) := by sorry

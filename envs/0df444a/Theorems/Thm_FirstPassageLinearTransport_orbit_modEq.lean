-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_modEq
-- name    : FirstPassageLinearTransport.orbit_modEq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:26.37328+00:00
-- url     : https://prove2.me/theorems/dc855943-7291-436c-b537-c2982a512135
-- title:
--   First Passage Linear Transport: orbit mod Eq
-- statement:
--   After `i` shortcut steps, `i` bits of modular information have been
--   consumed.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L70-L83
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L70-L83

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.orbit_modEq :
    ∀ i j n n' : ℕ, n ≡ n' [MOD 2 ^ (i + j)] →
      orbit i n ≡ orbit i n' [MOD 2 ^ j] := by sorry

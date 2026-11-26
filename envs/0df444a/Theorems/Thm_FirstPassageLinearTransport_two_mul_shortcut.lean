-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_mul_shortcut
-- name    : FirstPassageLinearTransport.two_mul_shortcut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:59:24.292207+00:00
-- url     : https://prove2.me/theorems/8a8300fc-141a-41d6-86c0-2264c18c3842
-- title:
--   First Passage Linear Transport: two mul shortcut
-- statement:
--   A division-free form of one shortcut step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L34-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L34-L38

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.two_mul_shortcut (n : ℕ) :
    2 * shortcut n = 3 ^ (n % 2) * n + n % 2 := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_div_two_pow_eq_exp
-- name    : FirstPassageLinearTransport.one_div_two_pow_eq_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:02.486367+00:00
-- url     : https://prove2.me/theorems/ad57d977-9799-5ea1-918a-913ede30f6b0
-- title:
--   First Passage Linear Transport: one div two pow eq exp
-- statement:
--   The First Passage Linear Transport construction uses the one div two pow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L58-L67
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TerminalProfile.lean#L58-L67

import Definitions.Def_FirstPassageLinearTransport_TerminalTail
import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.one_div_two_pow_eq_exp (q : ℕ) :
    1 / (2 : ℝ) ^ q = Real.exp (-(Real.log 2 * (q : ℝ))) := by sorry

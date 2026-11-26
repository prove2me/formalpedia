-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_boolParityWord
-- name    : FirstPassageLinearTransport.card_boolSupport_boolParityWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:25:20.800904+00:00
-- url     : https://prove2.me/theorems/cd365f44-a3f3-46d8-ad6c-b830be40d3a9
-- title:
--   First Passage Linear Transport: card bool Support bool Parity Word
-- statement:
--   The Boolean support of the actual parity word has cardinality equal to
--   the number of odd shortcut states.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L25-L42
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L25-L42

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_boolSupport_boolParityWord (m n : ℕ) :
    (boolSupport (boolParityWord m n)).card = oddCount n m := by sorry

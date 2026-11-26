-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_oddCount_mono
-- name    : FirstPassageLinearTransport.oddCount_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:59:29.511738+00:00
-- url     : https://prove2.me/theorems/9e079837-c6fe-43e8-962f-9df41b93f450
-- title:
--   First Passage Linear Transport: odd Count mono
-- statement:
--   The First Passage Linear Transport construction uses the odd Count mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L174-L179
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Parity.lean#L174-L179

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.NormNum.Parity
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.oddCount_mono {n a b : ℕ} (hab : a ≤ b) :
    oddCount n a ≤ oddCount n b := by sorry

-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_boolParityWord_tail
-- name    : FirstPassageLinearTransport.boolParityWord_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:17.732127+00:00
-- url     : https://prove2.me/theorems/52a294f0-7f3a-471d-bbfa-7bb1941858d1
-- title:
--   First Passage Linear Transport: bool Parity Word tail
-- statement:
--   The First Passage Linear Transport construction uses the bool Parity Word tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L392-L397
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Barrier.lean#L392-L397

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_Barrier
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators

theorem FirstPassageLinearTransport.boolParityWord_tail (r n : ℕ) :
    (fun i : Fin r => boolParityWord (r + 1) n i.succ) =
      boolParityWord r (shortcut n) := by sorry

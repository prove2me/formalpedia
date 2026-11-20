-- Prove2me | Theorems.Thm_DeletionCode_UniqueWordCount_repeatedWindow_card_le
-- name    : DeletionCode.UniqueWordCount.repeatedWindow_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:39:44.913173+00:00
-- url     : https://prove2.me/theorems/6543c5c4-e42f-41aa-b875-32c600df7bfb
-- title:
--   Unique Word Count: repeated Window card le
-- statement:
--   A fixed pair contributes at most 2^(n-k) words, with overlapping and
--   out-of-bounds pairs both handled explicitly.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L86-L108
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/UniqueWordCount.lean#L86-L108

import Definitions.Def_DeletionCode_FiniteConflictGraph
import Definitions.Def_DeletionCode_OverlapCollision
import Definitions.Def_DeletionCode_FinitePairUnion
import Definitions.Def_DeletionCode_UniqueWordParameters
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_DeletionCode_UniqueWordCount
set_option autoImplicit true
open DeletionCode DeletionCode.UniqueWordCount
open Windows HeaderRecovery
attribute [local instance] Classical.propDecidable

theorem DeletionCode.UniqueWordCount.repeatedWindow_card_le (n k : ℕ) (a b : Fin n) (hab : a < b) :
    (Finset.univ.filter (RepeatedWindow k a b)).card ≤ 2 ^ (n - k) := by sorry

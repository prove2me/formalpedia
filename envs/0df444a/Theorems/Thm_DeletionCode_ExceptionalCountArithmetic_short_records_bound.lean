-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalCountArithmetic_short_records_bound
-- name    : DeletionCode.ExceptionalCountArithmetic.short_records_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:44:50.20618+00:00
-- url     : https://prove2.me/theorems/53555932-0f62-4453-9d8a-df1bbbab4346
-- title:
--   Exceptional Count Arithmetic: short records bound
-- statement:
--   All smaller balanced edit counts contribute a lower power of n. Including
--   the unused zero-edit record is harmless and simplifies the upper bound.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalCountArithmetic.lean#L28-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalCountArithmetic.lean#L28-L43

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators

theorem DeletionCode.ExceptionalCountArithmetic.short_records_bound (n t : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) ≤
      t * 4 ^ (2 * t) * n ^ (2 * t - 1) := by sorry

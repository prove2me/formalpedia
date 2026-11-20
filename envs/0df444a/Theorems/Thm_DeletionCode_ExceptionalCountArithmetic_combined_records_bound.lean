-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalCountArithmetic_combined_records_bound
-- name    : DeletionCode.ExceptionalCountArithmetic.combined_records_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:45:59.687202+00:00
-- url     : https://prove2.me/theorems/a5c8dccd-5cf0-4bac-8c9e-ced93a5df2a3
-- title:
--   Exceptional Count Arithmetic: combined records bound
-- statement:
--   The close-anchor saving and the short-trace bound combine into one
--   constant times L*n^(2*t-1).
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalCountArithmetic.lean#L47-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalCountArithmetic.lean#L47-L59

import Definitions.Def_DeletionCode_FinitePairUnion
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_ExceptionalCountArithmetic
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalCountArithmetic
open scoped BigOperators

theorem DeletionCode.ExceptionalCountArithmetic.combined_records_bound (n t L : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    (∑ d ∈ Finset.range t, n ^ (2 * d) * 4 ^ (2 * d)) +
        (2 * t) * (2 * t + 2) * (2 * (4 * L)) * n ^ (2 * t - 1) * 4 ^ (2 * t) ≤
      exceptionalConstant t * L * n ^ (2 * t - 1) := by sorry

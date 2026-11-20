-- Prove2me | Theorems.Thm_DeletionCode_WitnessCounting_component_power_le
-- name    : DeletionCode.WitnessCounting.component_power_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:30:33.288551+00:00
-- url     : https://prove2.me/theorems/3cbb9950-7e42-41da-a2f7-a46f4caeb818
-- title:
--   Witness Counting: component power le
-- statement:
--   The large-size arithmetic premise pays for the one extra allowed component.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L97-L111
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCounting.lean#L97-L111

import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_WitnessCases
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_DeletionCode_WitnessCounting
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCounting
open Windows HeaderRecovery SignedRuleCount RuleSetGraph CountExponent
open ManuscriptCounting WitnessCases FiniteGenerating
open scoped BigOperators

theorem DeletionCode.WitnessCounting.component_power_le (t n k R c : ℕ) (hn : 1 ≤ n)
    (hbonus : windowLength k < R → n ≤ 2 ^ R)
    (hc : AllowedComponents t k R c) :
    n ^ c ≤ 2 ^ R * n ^ ((2 * t - 1) * R) := by sorry

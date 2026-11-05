-- Prove2me | Theorems.Thm_FloorRecurrence_floor_child_le_ratio
-- name    : FloorRecurrence.floor_child_le_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/ebd39b61-e2e4-4124-8610-cfbbff3cd77e
-- title:
--   FloorRecurrence: Floor child le ratio
-- statement:
--   Polynomial bounds for floor recurrences under explicit contraction, overhead, and finite base-case hypotheses. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L11-L17). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L11-L17 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators

theorem FloorRecurrence.floor_child_le_ratio (m t e : ℕ) (hm : 0 < m) :
    (FloorDepth.child m t e : ℝ) ≤ ((t : ℝ) / m) * e := by sorry

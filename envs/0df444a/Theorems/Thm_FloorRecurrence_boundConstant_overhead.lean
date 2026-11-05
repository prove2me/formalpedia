-- Prove2me | Theorems.Thm_FloorRecurrence_boundConstant_overhead
-- name    : FloorRecurrence.boundConstant_overhead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/0f2130d8-64c1-40e5-832f-33a9bddb3cf1
-- title:
--   FloorRecurrence: Bound Constant overhead
-- statement:
--   Polynomial bounds for floor recurrences under explicit contraction, overhead, and finite base-case hypotheses. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L89-L97). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorRecurrence.lean#L89-L97 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Definitions.Def_FloorDepth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FloorRecurrence
set_option autoImplicit true
open FloorRecurrence
open scoped BigOperators

theorem FloorRecurrence.boundConstant_overhead (m : ℕ) (f : ℕ → ℝ) (C γ : ℝ) (hγ : γ < 1) :
    C ≤ boundConstant m f C γ * (1 - γ) := by sorry

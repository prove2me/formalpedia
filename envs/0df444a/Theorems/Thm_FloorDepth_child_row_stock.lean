-- Prove2me | Theorems.Thm_FloorDepth_child_row_stock
-- name    : FloorDepth.child_row_stock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:10.380199+00:00
-- url     : https://prove2.me/theorems/3b7df854-5e44-4e29-917f-095365ccb90d
-- title:
--   FloorDepth: Child row stock
-- statement:
--   One exact row split leaves sufficient stock for every allowed child.
--
--   Executable depth for floor-child recursion, with monotonicity and exact row-stock transfer. These results retain their stated hypotheses and do not establish the complete fixed-tape multiplication algorithm.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorDepth.lean#L66-L79). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original authorship and assistance credits are retained in the upstream NOTICE and package documentation. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/machine-transfer-verification/transfer-proof/recurrence/FloorDepth.lean#L66-L79 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Order.Monotone.Basic
import Definitions.Def_FloorDepth
set_option autoImplicit true
open FloorDepth

theorem FloorDepth.child_row_stock (m tmax t e W R : ℕ) (htmax : tmax < m)
    (ht : t ≤ tmax) (he : m ≤ e) (hW : 0 < W)
    (stock : W ^ depth m tmax htmax e ∣ R) :
    W ^ depth m tmax htmax (child m t e) ∣ R / W := by sorry
